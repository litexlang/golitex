#!/usr/bin/env python3
"""Generate exhaustive, typed reading projections from the Rust evidence owners.

This development tool never runs in an installed reader. Generated matches and
complete struct patterns make new evidence fields/variants a compile-time
obligation. No human JSON, Rust Debug output or proof instances are parsed.
"""

from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent


def clean(source):
    pattern = r'//[^\n]*|/\*[\s\S]*?\*/|r\#*"[\s\S]*?"\#*|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])\''
    return re.sub(pattern, lambda match: ' ' * len(match[0]), source)


def closing(text, start):
    pairs = {'{': '}', '(': ')', '[': ']'}
    stack = [pairs[text[start]]]
    for index in range(start + 1, len(text)):
        char = text[index]
        if char in pairs:
            stack.append(pairs[char])
        elif char == stack[-1]:
            stack.pop()
            if not stack:
                return index
    raise ValueError(f'unclosed declaration at {start}')


def split(text, delimiter=','):
    items, start, stack = [], 0, []
    pairs = {'{': '}', '(': ')', '[': ']', '<': '>'}
    for index, char in enumerate(text):
        if char in pairs:
            stack.append(pairs[char])
        elif stack and char == stack[-1]:
            stack.pop()
        elif char == delimiter and not stack:
            items.append(text[start:index].strip())
            start = index + 1
    items.append(text[start:].strip())
    return [item for item in items if item]


def pieces_with_offsets(text):
    start, stack = 0, []
    pairs = {'{': '}', '(': ')', '[': ']', '<': '>'}
    for index, char in enumerate(text):
        if char in pairs:
            stack.append(pairs[char])
        elif stack and char == stack[-1]:
            stack.pop()
        elif char == ',' and not stack:
            yield start, index
            start = index + 1
    yield start, len(text)


def static_text(expression):
    literal = r'"(?:\\.|[^"\\])*"'
    match = re.fullmatch(r'\s*(?:return\s+)?text\(\s*(' + literal + r')\s*,\s*(' + literal + r')\s*,?\s*\)\s*;?\s*', expression, re.S)
    if not match:
        return None
    try:
        return {'name': json.loads(match[1]), 'message': json.loads(match[2])}
    except ValueError:
        return None


def fields(text):
    result = []
    for item in split(text):
        item = re.sub(r'#\[[^\]]*\]', '', item).strip()
        item = re.sub(r'^pub(?:\([^)]*\))?\s+', '', item)
        match = re.fullmatch(r'(\w+)\s*:\s*(.*)', item, re.S)
        if not match:
            raise ValueError(f'unrecognized named field: {item}')
        result.append((match[1], re.sub(r'\s+', ' ', match[2]).strip()))
    return result


def module_path(path):
    parts = list(path.relative_to(ROOT).with_suffix('').parts)
    if parts[-1] in ('mod', 'lib'):
        parts.pop()
    return 'crate' + ('::' + '::'.join(parts) if parts else '')


def use_items(text, prefix=''):
    output = {}
    for item in split(text):
        if '{' in item:
            position = item.index('{')
            stem = prefix + item[:position]
            output.update(use_items(item[position + 1:item.rindex('}')], stem))
        elif item and not item.endswith('*'):
            parts = re.split(r'\s+as\s+', item)
            value = prefix + parts[0]
            output[parts[-1].split('::')[-1]] = value
    return output


def inventory():
    types, by_name, imports, sources = {}, collections.defaultdict(list), {}, {}
    excluded = {'reading', 'compile_to_lean', 'compile_to_latex', 'json_output', 'knowledge_base'}
    for path in sorted(ROOT.rglob('*.rs')):
        if any(part in excluded for part in path.relative_to(ROOT).parts):
            continue
        source = path.read_text()
        text = clean(source)
        module = module_path(path)
        sources[module] = (path, source, text)
        uses = {}
        for match in re.finditer(r'\buse\s+([^;]+);', text):
            uses.update(use_items(match[1]))
        imports[module] = uses
        pattern = r'\bpub(?:\([^)]*\))?\s+(struct|enum)\s+(\w+)\s*([\{(;])'
        for match in re.finditer(pattern, text):
            kind, name, opener = match.groups()
            full = module + '::' + name
            if opener == ';':
                body = ''
            else:
                end = closing(text, match.end() - 1)
                body = text[match.end():end]
            record = {'name': name, 'module': module, 'kind': kind, 'opener': opener,
                      'fields': [], 'variants': [], 'file': path}
            if kind == 'struct':
                record['fields'] = fields(body) if opener == '{' else [(str(i), re.sub(r'^pub(?:\([^)]*\))?\s+', '', t)) for i, t in enumerate(split(body))]
            else:
                for entry in split(body):
                    entry = re.sub(r'#\[[^\]]*\]', '', entry).strip()
                    variant = re.match(r'(\w+)', entry)
                    if not variant:
                        raise ValueError(f'{full}: unrecognized variant {entry!r}')
                    tail = entry[variant.end():].strip()
                    shape = tail[:1]
                    data = fields(tail[1:-1]) if shape == '{' else [(str(i), t) for i, t in enumerate(split(tail[1:-1]))] if shape == '(' else []
                    record['variants'].append((variant[1], shape, data))
            types[full] = record
            by_name[name].append(full)
    return types, by_name, imports, sources


class Generator:
    def __init__(self):
        self.types, self.by_name, self.imports, self.sources = inventory()
        self.todo, self.done, self.unknown = [], set(), set()
        self.rules = []
        self.labels = {}
        registry = HERE / 'rule_ids.json'
        self.rule_ids = json.loads(registry.read_text()) if registry.exists() else {}
        self.paths, self.missing_exports = self.access_paths()
        self.methods = set()
        for path in ROOT.rglob('*.rs'):
            if 'reading' in path.parts:
                continue
            source = path.read_text()
            text = clean(source)
            for match in re.finditer(r'\bimpl\s+(\w+)\s*\{', text):
                end = closing(text, match.end() - 1)
                if re.search(r'pub fn rule_name_and_message\s*\(', text[match.end():end]):
                    self.methods.add(match[1])
                owner = self.resolve(match[1], module_path(path))
                if not owner:
                    continue
                impl_text = text[match.end():end]
                for method in re.finditer(r'pub fn rule_name_and_message_(en|zh|zh_hant|fr|ru|es|ar|ja|ko|vi)\s*\([^)]*\)[^{]*\{', impl_text):
                    start = match.end() + method.end()
                    method_end = closing(text, start - 1)
                    raw_body = source[start:method_end]
                    cleaned_body = text[start:method_end]
                    language = method[1].replace('_', '-')
                    direct = static_text(raw_body)
                    if direct:
                        self.labels[(owner, '', language)] = direct
                    dispatch = re.search(r'match\s+self\s*\{', cleaned_body)
                    if not dispatch:
                        continue
                    body_start = dispatch.end()
                    body_end = closing(cleaned_body, body_start - 1)
                    for arm_start, arm_end in pieces_with_offsets(cleaned_body[body_start:body_end]):
                        arm = raw_body[body_start + arm_start:body_start + arm_end]
                        variant = re.match(r'\s*Self::(\w+)[\s\S]*?=>', clean(arm))
                        if variant:
                            label = static_text(arm[variant.end():])
                            if label:
                                self.labels[(owner, variant[1], language)] = label

    def access_paths(self):
        aliases = {full: full for full in self.types}
        declarations, exports = {}, []
        for module, (_, _, source) in self.sources.items():
            if module == 'crate::prelude':
                continue
            for match in re.finditer(r'\b(pub(?:\([^)]*\))?\s+)?mod\s+(\w+)\s*;', source):
                declarations[module + '::' + match[2]] = match[1] or ''
            for match in re.finditer(r'\bpub(?:\([^)]*\))?\s+use\s+([^;]+);', source):
                exports.append((module, match[1]))
        for _ in range(12):
            changed = False
            for module, statement in exports:
                if statement.strip().endswith('::*'):
                    raw = statement.strip()[:-3]
                    owner = module
                    while raw.startswith('super::'):
                        raw = raw[7:]
                        owner = owner.rsplit('::', 1)[0]
                    target = raw if raw.startswith('crate::') else owner + '::' + raw.removeprefix('self::')
                    found = [(alias.rsplit('::', 1)[1], full) for alias, full in list(aliases.items()) if alias.rsplit('::', 1)[0] == target]
                else:
                    found = []
                    for name, raw in use_items(statement).items():
                        full = self.resolve(raw, module)
                        if full:
                            found.append((name, full))
                for name, full in found:
                    alias = module + '::' + name
                    if aliases.get(alias) != full:
                        aliases[alias] = full
                        changed = True
            if not changed:
                break
        def accessible(alias):
            segments = alias.split('::')[:-1]
            for length in range(3, len(segments) + 1):
                visibility = declarations.get('::'.join(segments[:length]), 'pub ')
                if not visibility.startswith('pub') or visibility.startswith(('pub(in ', 'pub(super)')):
                    return False
            return True
        candidates = collections.defaultdict(list)
        for alias, full in aliases.items():
            if accessible(alias):
                candidates[full].append(alias)
        paths, missing = {}, {}
        for full in self.types:
            if candidates[full]:
                paths[full] = min(candidates[full], key=lambda path: (path.count('::'), len(path), path))
            else:
                paths[full] = full
                missing[full] = str(self.types[full]['file'].relative_to(ROOT))
        return paths, missing

    def resolve(self, raw, module, seen=None):
        raw = raw.strip()
        seen = seen or set()
        if (raw, module) in seen or len(seen) > 64:
            return None
        seen.add((raw, module))
        if raw.startswith('crate::'):
            full = raw
        elif raw.startswith('super::'):
            return self.resolve(raw[7:], module.rsplit('::', 1)[0], seen)
        elif raw.startswith('self::'):
            return self.resolve(raw[6:], module, seen)
        else:
            head, *tail = raw.split('::', 1)
            target = self.imports.get(module, {}).get(head)
            if target:
                target = target + ('::' + tail[0] if tail else '')
                found = self.resolve(target, module, seen)
                if found:
                    return found
            full = module + '::' + raw
        if full in self.types:
            return full
        owner, _, name = full.rpartition('::')
        target = self.imports.get(owner, {}).get(name)
        if target:
            found = self.resolve(target, owner, seen)
            if found:
                return found
        name = raw.split('::')[-1]
        candidates = self.by_name.get(name, [])
        if len(candidates) == 1:
            return candidates[0]
        return None

    def function(self, full):
        return 'capture_' + full.removeprefix('crate::').replace('::', '__')

    def expression(self, raw, expression, module):
        raw = raw.strip()
        if raw.startswith('&'):
            return self.expression(raw[1:].removeprefix('mut ').strip(), expression, module)
        leaf = raw.split('::')[-1]
        primitives = {'String', 'str', 'PlainName', 'ObjIR'}
        if leaf in primitives:
            return f'JsonValue::String(({expression}).to_string())'
        if raw == 'bool':
            return f'JsonValue::Bool(*({expression}))'
        if raw in {'usize', 'u64', 'u32', 'u16', 'u8', 'i64', 'i32', 'f64', 'isize', 'i128', 'u128'}:
            return f'JsonValue::String(({expression}).to_string())'
        if leaf == 'PathBuf':
            return f'JsonValue::String(({expression}).display().to_string())'
        special = {'FactId': 'fact_reference', 'IdentifierId': 'identifier_id',
                   'WellDefinednessId': 'wd_reference', 'SourceLine': 'source_line',
                   'CodeSource': 'code_source', 'ExecEnv': 'environment',
                   'BoundName': 'bound_name', 'IdentifierObj': 'identifier',
                   'AtomicName': 'atomic_name', 'StandardSet': 'standard_set'}
        if leaf in special:
            return f'capture.{special[leaf]}({expression}, runtime)'
        if leaf in {'RuntimeError', 'RuntimeParseError'}:
            return f'JsonValue::String(({expression}).to_string())'
        if leaf == 'EvalRational':
            return f'JsonValue::String(({expression}).to_obj().readable_string())'
        if raw == '()':
            return 'JsonValue::Null'
        if raw.startswith('(') and raw.endswith(')'):
            pieces = split(raw[1:-1])
            children = [self.expression(t, f'&({expression}).{i}', module) for i, t in enumerate(pieces)]
            return 'JsonValue::Array(vec![' + ', '.join(children) + '])'
        generic = re.fullmatch(r'([\w:]+)\s*<([\s\S]*)>', raw)
        if generic:
            shell, inner = generic.groups()
            shell = shell.split('::')[-1]
            args = split(inner)
            if shell in {'Box', 'Rc', 'Arc', 'RefCell', 'Cell'}:
                return self.expression(args[0], expression, module)
            if shell == 'Option':
                child = self.expression(args[0], 'item', module)
                return f'match ({expression}).as_ref() {{ Some(item) => {child}, None => JsonValue::Null }}'
            if shell in {'Vec', 'HashSet', 'BTreeSet'}:
                child = self.expression(args[0], 'item', module)
                return f'JsonValue::Array(({expression}).iter().map(|item| {child}).collect())'
            if shell in {'HashMap', 'BTreeMap'}:
                key = self.expression(args[0], 'key', module)
                value = self.expression(args[1], 'item', module)
                return f'{{ let mut entries = ({expression}).iter().map(|(key, item)| JsonValue::Array(vec![{key}, {value}])).collect::<Vec<_>>(); entries.sort_by_key(JsonValue::stringify); JsonValue::Array(entries) }}'
            if shell == 'Result':
                ok = self.expression(args[0], 'item', module)
                err = self.expression(args[1], 'item', module)
                return f'match {expression} {{ Ok(item) => node("Result", "Ok", vec![("value", {ok})]), Err(item) => node("Result", "Err", vec![("value", {err})]) }}'
            if shell == 'Range':
                return f'node("Range", "", vec![("start", JsonValue::String(({expression}).start.to_string())), ("end", JsonValue::String(({expression}).end.to_string()))])'
        full = self.resolve(raw, module)
        if full:
            if full not in self.done and full not in self.todo:
                self.todo.append(full)
            return f'{self.function(full)}({expression}, capture, runtime)'
        self.unknown.add((raw, module))
        return f'capture.unavailable({json.dumps(raw)})'

    def branch(self, record, full, name, shape, data):
        prefix = self.paths[full] + ('::' + name if record['kind'] == 'enum' else '')
        bindings = [f'f{i}' for i in range(len(data))]
        if shape == '{':
            pattern = prefix + ' { ' + ', '.join(f'{field}: {binding}' for (field, _), binding in zip(data, bindings)) + ' }'
        elif shape == '(':
            pattern = prefix + '(' + ', '.join(bindings) + ')'
        else:
            pattern = prefix
        lines = [pattern + ' => {']
        locations = [(binding, raw) for (_, raw), binding in zip(data, bindings) if re.search(r'\bSourceLine\b', raw)]
        if locations:
            binding, raw = locations[0]
            if 'Option' in raw:
                lines.append(f'let saved_location = {binding}.as_ref().map(|line| capture.enter_location(line));')
            else:
                lines.append(f'let saved_location = Some(capture.enter_location({binding}));')
        environments = [binding for (_, raw), binding in zip(data, bindings) if re.search(r'\bExecEnv\b', raw)]
        if environments:
            lines.append('let saved_scope = capture.enter_scope();')
            for binding in environments:
                lines.append(f'capture.index_environment({binding}, runtime);')
        is_infer = record['name'].startswith('Infer') and record['name'].endswith('Result')
        is_theorem = record['name'] == 'BuiltinTheoremId'
        is_rule = record['kind'] == 'enum' and ('SearchProofByBuiltinRule' in record['name'] or record['name'] == 'EqualitySearchProofByBuiltinRule' or is_infer or is_theorem)
        if is_rule:
            # A leaf inference payload is commonly a struct named Infer*Result.
            # Only another rule *dispatcher enum* defers catalogue ownership.
            payloads = [self.resolve(token, record['module']) for _, raw in data for token in re.findall(r'[\w:]+', raw)]
            nested = any(payload and self.types[payload]['kind'] == 'enum' and
                         ('SearchProofByBuiltinRule' in self.types[payload]['name'] or
                          (is_infer and self.types[payload]['name'].startswith('Infer') and self.types[payload]['name'].endswith('Result')))
                         for payload in payloads)
            if not nested:
                key = record['name'] + '::' + name
                category = 'infer' if is_infer else 'builtin_theorem' if is_theorem else 'builtin'
                registry_key = category + '.' + key
                rule_id = self.rule_ids.setdefault(registry_key, registry_key)
                labels = {}
                for language in ['en', 'zh', 'zh-hant', 'fr', 'ru', 'es', 'ar', 'ja', 'ko', 'vi']:
                    label = self.labels.get((full, name, language))
                    if not label and len(data) == 1:
                        payload = self.resolve(data[0][1], record['module'])
                        label = self.labels.get((payload, '', language))
                    if label:
                        labels[language] = label
                self.rules.append({'id': rule_id, 'category': category, 'family': record['name'], 'variant': name, 'labels': labels})
                lines.append(f'let rule_id = Some({json.dumps(rule_id)});')
            else:
                lines.append('let rule_id = None;')
        declaration_type = record['name'] in {
            'DefPropStmt', 'DefAbstractPropStmt', 'DefStructStmt', 'DefTemplateStmt', 'DefThmStmt', 'AxiomStmt', 'DefStrategyStmt',
            'HaveObjInNonemptySetOrParamTypeStmt', 'HaveObjEqualStmt', 'HaveObjByExistFactsStmt', 'TrustHaveStmt',
            'HaveByReplacementAxiomStmt', 'LetObjStmt', 'HaveFnEqualStmt', 'HaveFnEqualCaseByCaseStmt',
            'HaveFnByForallExistUniqueStmt', 'HaveFnByInducStmt',
        }
        if declaration_type:
            lines.append('capture.source_snapshot_depth += 1;')
        text = []
        for (field, raw), binding in zip(data, bindings):
            raw = re.sub(r'\bSelf\b', full, raw)
            value = self.expression(raw, binding, record['module'])
            if record['name'] in {'FormedAtomicSubject', 'FormedFunctionArgument'} and field == 'wd_id':
                value = f'capture.wd_identity({binding}, runtime)'
            if full.startswith('crate::ast::fact::') and field == 'fact_id' and raw == 'FactId':
                # An AST subject's own identity is not a citation. Temporary
                # calculation subjects need not have been stored in an Env.
                value = f'super::helper::object(vec![("kind", JsonValue::String("fact_identity".into())), ("fact_id", JsonValue::String({binding}.to_string()))])'
            if full.startswith('crate::ast::') and raw == 'Vec<Stmt>':
                value = f'capture.ast_body({json.dumps(field)}, {binding}, runtime)'
            if full.startswith('crate::ast::') and raw == 'Option<Vec<Stmt>>':
                value = f'match {binding} {{ Some(body) => capture.ast_body({json.dumps(field)}, body, runtime), None => JsonValue::Null }}'
            if full.startswith('crate::ast::') and raw == 'Vec<Vec<Stmt>>':
                value = f'JsonValue::Array(({binding}).iter().enumerate().map(|(index, body)| capture.ast_body(&format!("{field}:{{index}}"), body, runtime)).collect())'
            if re.fullmatch(r'Vec<(?:crate::execute::)?ExecStmtResult>', raw):
                value = f'capture.proof_steps({json.dumps(record["name"])}, {binding}, runtime)'
            if record['name'] == 'ExecByCasesStmtSuccess' and field == 'branches':
                child = self.expression('ByCasesBranchSuccess', 'item', record['module'])
                value = f'JsonValue::Array(({binding}).iter().enumerate().map(|(index, item)| {{ let saved = capture.proof_branch.replace(index); let value = {child}; capture.proof_branch = saved; value }}).collect())'
            if record['name'] == 'ByInducBodySuccess' and field in {'base', 'step'}:
                value = f'{{ let saved = std::mem::replace(&mut capture.proof_part, {json.dumps(field)}.into()); let value = {value}; capture.proof_part = saved; value }}'
            if record['name'] in {'DefPropStmt', 'DefAbstractPropStmt', 'DefStructStmt', 'DefTemplateStmt', 'DefThmStmt', 'AxiomStmt', 'DefStrategyStmt'} and field in {'name', 'template_name'}:
                value = f'capture.named_definition({binding}, {json.dumps(record["name"])}, runtime)'
            if not full.startswith('crate::ast::') and field in {'statement', 'stmt'}:
                value = '{ capture.source_snapshot_depth += 1; let value = ' + value + '; capture.source_snapshot_depth -= 1; value }'
            if field == 'stored_fact_ids':
                value = '{ capture.subject_depth += 1; let value = ' + value + '; capture.subject_depth -= 1; value }'
                if raw == 'Vec<FactId>':
                    value = '{ let value = ' + value + f'; capture.stored({binding}); value }}'
            text.append(f'({json.dumps(field)}, {value})')
        lines.append('let fields = vec![' + ', '.join(text) + '];')
        if declaration_type:
            lines.append('capture.source_snapshot_depth -= 1;')
        lines.append(f'let mut output = node({json.dumps(record["name"])}, {json.dumps(name)}, fields);')
        if declaration_type and locations:
            binding, raw = locations[0]
            lines.append(f'let declaration = capture.declaration_reference({binding}, {json.dumps(record["name"])}); if let JsonValue::Object(fields) = &mut output {{ fields.insert("declaration".into(), declaration); }}')
        if record['name'] == 'PredicateSignatureWellDefinedProof' and name in {'Prop', 'AbstractProp'}:
            predicate = bindings[[field for field, _ in data].index('predicate')]
            lines.append(f'let declaration = capture.signature_declaration({predicate}, runtime); if let JsonValue::Object(fields) = &mut output {{ fields.insert("declaration".into(), declaration); }}')
        if record['name'] == 'StoreFactResult':
            lines.append('capture.stored(&value.stored_fact_ids());')
        if record['name'] == 'StoreFactAndInferResult':
            lines.append('capture.record_inference(value, &output, runtime);')
        if record['name'] == 'StoreInferredFactResult':
            lines.append('if let JsonValue::Object(fields) = &mut output { fields.insert("stored_fact_ids".into(), JsonValue::Array(value.stored_fact_ids().iter().map(|id| JsonValue::String(id.to_string())).collect())); }')
        if record['name'] == 'AssumeDomFactResult':
            lines.append('capture.fact_context(&value.store_and_infer, "hypothesis", &output, "well_defined");')
        if record['name'] == 'ProveAndStoreThenFactResult':
            lines.append('capture.fact_context(&value.store_and_infer, "verified", &output, "verify_result");')
        if record['name'] == 'ExecFactStmtSuccessResult':
            lines.append('capture.fact_context(&value.store_and_infer_result, "verified", &output, "verify_result");')
        if record['name'] == 'StoreHaveObjAndInferResult':
            lines.append('for stored in &value.store_and_infer_results { capture.fact_context(stored, "declaration", &output, ""); }')
        if record['name'] in {'FormedAtomicSubject', 'FormedFunctionArgument'}:
            lines.append('capture.wd_registration(&value.wd_id, &output);')
        if record['name'] == 'FnObjDomainCheckResult':
            lines.append('if let Some(stages) = capture.evidence_field(&output, "stages") { if let Some(JsonValue::Array(children)) = capture.evidence_field(&stages, "child_obj_well_defined") { for formed in &value.scope.formed_children { if let Some(child) = children.get(formed.child_index) { capture.wd_evidence(&formed.wd_id, child, "well_definedness"); } } } }')
        if {'argument_scope', 'child_obj_well_defined'}.issubset({field for field, _ in data}):
            scope_binding = bindings[[field for field, _ in data].index('argument_scope')]
            lines.append(f'if let Some(scope) = {scope_binding}.as_ref() {{ if let Some(JsonValue::Array(children)) = capture.evidence_field(&output, "child_obj_well_defined") {{ for formed in &scope.formed_children {{ if let Some(child) = children.get(formed.child_index) {{ capture.wd_evidence(&formed.wd_id, child, "well_definedness"); }} }} }} }}')
        if record['name'] in {'Fact', 'AtomicFact', 'Obj', 'Stmt'}:
            lines.append('if let JsonValue::Object(fields) = &mut output { fields.insert("text".into(), JsonValue::String(value.readable_string())); }')
        if record['name'] == 'Fact':
            lines.append('capture.subject(value, runtime);')
        if record['name'] == 'AtomicFact':
            lines.append('capture.subject(&value.clone().into(), runtime);')
        if is_rule:
            if record['name'] in self.methods:
                lines.append('if let Some(rule_id) = rule_id { let text = value.rule_name_and_message(runtime.launch_command.output_language()); capture.rule_application(&mut output, rule_id, &text.rule_name, &text.message); }')
            else:
                lines.append(f'if let Some(rule_id) = rule_id {{ capture.rule_application(&mut output, rule_id, {json.dumps(name)}, ""); }}')
        if environments:
            lines.append('capture.leave_scope(saved_scope);')
        if locations:
            lines.append('if let Some(location) = saved_location { capture.leave_location(location); }')
        lines.append('output')
        lines.append('},')
        return '\n'.join(lines)

    def generate(self):
        for raw in ['ExecStmtResult', 'Stmt']:
            full = self.resolve(raw, 'crate')
            if full is None:
                raise ValueError(raw)
            self.todo.append(full)
        functions = []
        while self.todo:
            full = self.todo.pop(0)
            if full in self.done:
                continue
            self.done.add(full)
            record = self.types[full]
            variants = record['variants'] if record['kind'] == 'enum' else [('', record['opener'], record['fields'])]
            branches = [self.branch(record, full, *variant) for variant in variants]
            if record['kind'] == 'enum' and not branches:
                functions.append(f'pub(super) fn {self.function(full)}(value: &{self.paths[full]}, _capture: &mut Capture, _runtime: &Runtime) -> JsonValue {{ match *value {{}} }}')
                continue
            subject = full.startswith('crate::ast::') or record['name'] == 'StoreFactResult'
            before = 'capture.subject_depth += 1;\n' if subject else ''
            after = 'capture.subject_depth -= 1;\n' if subject else ''
            if record['name'] == 'Stmt':
                before += 'let source_frame = capture.begin_ast_statement(value, runtime);\n'
                after += 'capture.end_ast_statement(source_frame, &output);\n'
            functions.append(f'pub(super) fn {self.function(full)}(value: &{self.paths[full]}, capture: &mut Capture, runtime: &Runtime) -> JsonValue {{\n{before}let output = match value {{\n' + '\n'.join(branches) + '\n};\n' + after + 'capture.intern_evidence(output)\n}')
        header = '// Generated by generate_capture.py. Do not edit; regenerate after evidence changes.\n#![allow(unused_mut, unused_variables, non_snake_case, clippy::all)]\nuse crate::prelude::*;\nuse super::capture::Capture;\nuse super::helper::node;\n\n'
        return header + '\n\n'.join(functions) + '\n'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    generator = Generator()
    output = generator.generate()
    catalogue = json.dumps(sorted(generator.rules, key=lambda item: item['id']), indent=2) + '\n'
    paths = {HERE / 'capture_generated.rs': output, HERE / 'rule_catalogue_generated.json': catalogue}
    paths[HERE / 'rule_ids.json'] = json.dumps(dict(sorted(generator.rule_ids.items())), indent=2) + '\n'
    for path, contents in paths.items():
        if args.check:
            if not path.exists() or path.read_text() != contents:
                raise SystemExit(f'{path.name} is stale; run python3 src/reading/generate_capture.py')
        else:
            path.write_text(contents)
    print(f'{len(generator.done)} evidence/AST types, {len(generator.rules)} rule variants, {len(generator.unknown)} unsupported field types')
    for raw, module in sorted(generator.unknown):
        print(f'UNSUPPORTED {raw} in {module}')
    for full in sorted(generator.done.intersection(generator.missing_exports)):
        print(f'PRIVATE {full}')


if __name__ == '__main__':
    main()
