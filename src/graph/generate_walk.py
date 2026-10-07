#!/usr/bin/env python3
"""Generate a read-only, exhaustive visitor over the current typed certificates.

No display/JSON text is parsed by the Rust graph consumer. New fields and enum
variants are regenerated from their producer shapes; compilation checks access.
"""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]


def clean(source):
    source = re.sub(r'/\*.*?\*/', '', source, flags=re.S)
    return re.sub(r'//[^\n]*', '', source)


def split(text, separator=','):
    result, start, depth = [], 0, 0
    for index, char in enumerate(text):
        if char in '({[<':
            depth += 1
        elif char in ')}]>':
            depth -= 1
        elif char == separator and depth == 0:
            result.append(text[start:index].strip())
            start = index + 1
    if text[start:].strip():
        result.append(text[start:].strip())
    return result


def closing(text, start):
    depth = 1
    for index in range(start + 1, len(text)):
        if text[index] == '{':
            depth += 1
        elif text[index] == '}':
            depth -= 1
            if depth == 0:
                return index
    raise ValueError('unclosed type body')


def expand_use(text, prefix=''):
    result = []
    for part in split(text):
        if '{' in part:
            before, body = part.split('{', 1)
            result.extend(expand_use(body.rsplit('}', 1)[0], prefix + before))
        else:
            path, *alias = part.split(' as ')
            path = prefix + path.strip()
            result.append((path, alias[0].strip() if alias else path.split('::')[-1]))
    return result


modules = {}
types = {}


def load_module(key, path, accessible):
    source = clean(path.read_text())
    symbols, exports, imports = {}, {}, []
    modules[key] = (symbols, exports, imports, accessible)
    for match in re.finditer(r'\bpub(?:\([^)]*\))?\s+(struct|enum)\s+(\w+)\s*\{', source):
        kind, name = match.group(1, 2)
        start = match.end() - 1
        body = source[start + 1:closing(source, start)]
        fields = []
        if kind == 'struct':
            for item in split(body):
                item = re.sub(r'#\[[^]]*\]\s*', '', item)
                field = re.fullmatch(r'(?:pub(?:\([^)]*\))?\s+)?(\w+)\s*:\s*(.+)', item, flags=re.S)
                if field:
                    fields.append((field.group(1), field.group(2).strip()))
        else:
            for item in split(body):
                item = re.sub(r'#\[[^]]*\]\s*', '', item)
                variant = re.match(r'(\w+)\s*(.*)', item, flags=re.S)
                if not variant:
                    continue
                vname, tail = variant.group(1, 2)
                if tail.startswith('('):
                    parts = [(str(i), t) for i, t in enumerate(split(tail[1:-1]))]
                    fields.append((vname, 'tuple', parts))
                elif tail.startswith('{'):
                    parts = []
                    for field in split(tail[1:-1]):
                        fname, ftype = field.split(':', 1)
                        parts.append((fname.strip(), ftype.strip()))
                    fields.append((vname, 'named', parts))
                else:
                    fields.append((vname, 'unit', []))
        full = key + '::' + name
        types[full] = (key, name, kind, fields)
        symbols[name] = full
        exports[name] = full
    for match in re.finditer(r'(\bpub(?:\([^)]*\))?\s+)?use\s+([^;]+);', source):
        public = bool(match.group(1)) and 'pub(in ' not in (match.group(1) or '')
        imports.extend((p, alias, public) for p, alias in expand_use(match.group(2)))
    for match in re.finditer(r'(\bpub(?:\([^)]*\))?\s+)?mod\s+(\w+)\s*;', source):
        name = match.group(2)
        directory = path.parent if path.name in ('lib.rs', 'mod.rs') else path.parent / path.stem
        child = directory / (name + '.rs')
        if not child.exists():
            child = directory / name / 'mod.rs'
        if child.exists():
            load_module(key + '::' + name, child, accessible and bool(match.group(1)))


load_module('crate', ROOT / 'src/lib.rs', True)


def absolute(path, module):
    if path.startswith('crate::'):
        return path
    if path.startswith('self::'):
        return module + path[4:]
    while path.startswith('super::'):
        module = module.rsplit('::', 1)[0]
        path = path[7:]
    return module + '::' + path


def resolve(path, module):
    full = absolute(path, module)
    if full in types:
        return full
    owner, name = full.rsplit('::', 1)
    if owner in modules:
        return modules[owner][0].get(name)
    return None


for _ in range(30):
    changed = False
    for module, (symbols, exports, imports, _) in modules.items():
        for path, alias, public in imports:
            if alias == '*':
                owner = absolute(path[:-3], module)
                additions = modules.get(owner, ({}, {}, [], False))[1]
            else:
                target = resolve(path, module)
                additions = {alias: target} if target else {}
            for name, target in list(additions.items()):
                if symbols.get(name) != target:
                    symbols[name] = target
                    changed = True
                if public:
                    exports[name] = target
    if not changed:
        break

aliases = {}
for module, (_, exports, _, accessible) in modules.items():
    if accessible:
        for name, target in exports.items():
            candidate = module + '::' + name
            if target not in aliases or len(candidate) < len(aliases[target]):
                aliases[target] = candidate

SPECIAL = {'FactId', 'AtomicName', 'IdentifierObj', 'ExecStmtResult', 'StoreFactAndInferResult', 'AssumeDomFactResult', 'StoreHaveObjAndInferResult', 'BuiltinThmApplication', 'TheoremCall'}
SKIP = {'ExecEnv', 'SourceLine', 'Stmt', 'Runtime', 'WellDefinednessId', 'IdentifierId'}


def shape(type_text, module):
    value = re.sub(r'\s+', '', type_text)
    if value.startswith('(') and value.endswith(')'):
        return ('tuple', [shape(t, module) for t in split(value[1:-1])])
    container = re.fullmatch(r'(?:[\w:]+::)?(Vec|Box|Option|Rc)<(.+)>', value)
    if container:
        return (container.group(1), shape(container.group(2), module))
    name = value.split('::')[-1]
    if name in SKIP:
        return ('skip', name)
    if name in SPECIAL:
        return ('special', name)
    target = resolve(value, module)
    return ('type', target) if target else ('skip', value)


relevant = set()


def useful(node):
    kind, val = node
    if kind == 'special':
        return True
    if kind == 'type':
        return val in relevant
    if kind == 'tuple':
        return any(useful(child) for child in val)
    if kind in ('Vec', 'Box', 'Rc', 'Option'):
        return useful(val)
    return False


for _ in range(60):
    before = len(relevant)
    for full, (module, name, kind, fields) in types.items():
        if name in SKIP or name in SPECIAL:
            continue
        children = fields if kind == 'struct' else [f for v, _, group in fields if not v.startswith('Fail') and v not in ('Failed', 'NotFound', 'Unknown', 'Unsupported') for f in group]
        if any(useful(shape(t, module)) for _, t in children):
            relevant.add(full)
    if len(relevant) == before:
        break

roots = ['crate::execute::exec_stmt_result::ExecStmtResult', 'crate::exec_env::exec_env::StoredIdentifierDefinition',
         'crate::ast::stmt::DefStrategyStmt', 'crate::ast::stmt::DefAlgoByCasesStmt', 'crate::ast::stmt::DefAlgoByInducStmt', 'crate::ast::stmt::DefPropStmt', 'crate::ast::stmt::DefThmStmt', 'crate::ast::stmt::DefAbstractPropStmt',
         'crate::ast::stmt::DefStructStmt', 'crate::ast::stmt::DefTemplateStmt', 'crate::ast::stmt::AxiomStmt',
         'crate::ast::fact::fact::Fact', 'crate::store_fact_and_infer::store_fact_and_infer_result::infer_fact_result::InferFactResult']
selected = set()


def include(full):
    if full in selected:
        return
    selected.add(full)
    module, _, kind, fields = types[full]
    children = fields if kind == 'struct' else [f for v, _, group in fields if not v.startswith('Fail') and v not in ('Failed', 'NotFound', 'Unknown', 'Unsupported') for f in group]
    for _, text in children:
        include_shape(shape(text, module))


def include_shape(node):
    kind, val = node
    if kind == 'type' and val in relevant:
        include(val)
    elif kind == 'tuple':
        for child in val:
            include_shape(child)
    elif kind in ('Vec', 'Box', 'Rc', 'Option'):
        include_shape(val)


for root in roots:
    include(root)


def function(full):
    name = types[full][1]
    base = 'walk_' + re.sub(r'(?<!^)(?=[A-Z])', '_', name).lower()
    duplicates = [key for key in selected if types[key][1] == name]
    return base if len(duplicates) == 1 else base + '_' + str(sorted(duplicates).index(full))


counter = 0


FACT_LEAVES = {types[k][1] for k in types if k.startswith('crate::ast::fact::atomic::') and types[k][2] == 'struct' and any(n == 'fact_id' for n, _ in types[k][3])}
SUBJECT_FIELDS = {'fact', 'goal', 'equal_fact', 'type_fact', 'rewritten_fact', 'rewritten_equal', 'target', 'requirement_facts', 'dom_facts', 'conclusions', 'then_facts', 'assumption', 'assumption_components'}

def field_source(node, field, expression, module, indent):
    kind, target = node
    if (module.startswith('crate::execute') or module.startswith('crate::exec_env')) and field not in SUBJECT_FIELDS and kind == 'type' and target and types[target][1] in FACT_LEAVES:
        return [' ' * indent + f'graph.reference_fact(&({expression}).fact_id, runtime, locals, refs, outputs);']
    return []

def emit(node, expression, indent):
    global counter
    kind, val = node
    if not useful(node):
        return []
    pad = ' ' * indent
    if kind == 'special':
        if val == 'TheoremCall':
            return [pad + f'graph.reference_theorem_call({expression}, runtime, locals, refs);']
        if val == 'BuiltinThmApplication':
            return [pad + f'graph.reference_builtin_theorem({expression}, refs);']
        if val == 'StoreHaveObjAndInferResult':
            return [pad + f'graph.collect_stored_ids(&({expression}).stored_fact_ids, runtime, locals, refs, outputs);']
        if val == 'ExecStmtResult':
            return [pad + f'graph.collect_statement({expression}, runtime, locals);']
        method = {'FactId': 'reference_fact', 'AtomicName': 'reference_name', 'IdentifierObj': 'reference_identifier',
                  'StoreFactAndInferResult': 'collect_store', 'AssumeDomFactResult': 'collect_assumption'}[val]
        return [pad + f'graph.{method}({expression}, runtime, locals, refs, outputs);']
    if kind == 'type':
        if val not in aliases:
            module, name, type_kind, fields = types[val]
            assert type_kind == 'struct', val
            counter += 1
            local = f'payload{counter}'
            result = [pad + '{', pad + f'    let {local} = {expression};']
            envs = [n for n, t in fields if re.sub(r'\s+', '', t) == 'Box<ExecEnv>']
            if envs:
                result.append(pad + '    let mut scope_envs = locals.to_vec();')
                for n in envs:
                    result.append(pad + f'    scope_envs.push({local}.{n}.as_ref());')
                result.append(pad + '    let locals = scope_envs.as_slice();')
            for n, text in fields:
                if n == 'fact_id' and module.startswith('crate::ast'):
                    continue
                if n == 'defined_params' and shape(text, module) == ('special', 'StoreHaveObjAndInferResult'):
                    result.append(pad + f'    graph.collect_bound_parameters(&{local}.{n}.stored_fact_ids, runtime, locals);')
                    continue
                if n == 'stored_fact_ids' and re.sub(r'\s+', '', text) == 'Vec<FactId>':
                    result.append(pad + f'    graph.collect_stored_ids(&{local}.{n}, runtime, locals, refs, outputs);')
                    continue
                if shape(text, module) == ('special', 'AtomicName') and (name == 'StructObj' or n == 'struct_name' or n == 'template_name'):
                    method = 'reference_template_name' if n == 'template_name' else 'reference_struct_name'
                    result.append(pad + f'    graph.{method}(&{local}.{n}, runtime, locals, refs, outputs);')
                    continue
                result.extend(field_source(shape(text, module), n, f'&{local}.{n}', module, indent + 4))
                result.extend(emit(shape(text, module), f'&{local}.{n}', indent + 4))
            return result + [pad + '}']
        return [pad + f'{function(val)}({expression}, graph, runtime, locals, refs, outputs);']
    if kind == 'tuple':
        lines = []
        for i, child in enumerate(val):
            lines.extend(emit(child, f'&({expression}).{i}', indent))
        return lines
    if kind in ('Box', 'Rc'):
        return emit(val, f'({expression}).as_ref()', indent)
    counter += 1
    var = f'child{counter}'
    start = f'for {var} in ({expression}).iter() {{' if kind == 'Vec' else f'if let Some({var}) = ({expression}).as_ref() {{'
    return [pad + start] + emit(val, var, indent + 4) + [pad + '}']


lines = ['//! Generated typed graph reference visitor. Run src/graph/generate_walk.py.',
         '#![allow(unused_variables)]', '', 'use super::math_graph::{MathGraph, GraphReference};',
         'use crate::exec_env::ExecEnv;', 'use crate::runtime::Runtime;', '']
missing = [full for full in sorted(selected) if full not in aliases and types[full][2] != 'struct']
if missing:
    print('Missing exports:', len(missing))
    print('\n'.join(missing))
    raise SystemExit(1)
for full in sorted(selected):
    module, name, kind, fields = types[full]
    if full not in aliases:
        continue
    lines += [f'pub(super) fn {function(full)}(value: &{aliases[full]}, graph: &mut MathGraph, runtime: &Runtime, locals: &[&ExecEnv], refs: &mut Vec<GraphReference>, outputs: &mut Vec<String>) {{']
    if kind == 'struct':
        envs = [(n, t) for n, t in fields if re.sub(r'\s+', '', t) == 'Box<ExecEnv>']
        if envs:
            lines.append('    let mut scope_envs = locals.to_vec();')
            for n, _ in envs:
                lines.append(f'    scope_envs.push(value.{n}.as_ref());')
            lines.append('    let locals = scope_envs.as_slice();')
        for n, text in fields:
            if n == 'fact_id' and module.startswith('crate::ast'):
                continue
            if n == 'defined_params' and shape(text, module) == ('special', 'StoreHaveObjAndInferResult'):
                lines.append(f'    graph.collect_bound_parameters(&value.{n}.stored_fact_ids, runtime, locals);')
                continue
            if n == 'stored_fact_ids' and re.sub(r'\s+', '', text) == 'Vec<FactId>':
                lines.append(f'    graph.collect_stored_ids(&value.{n}, runtime, locals, refs, outputs);')
                continue
            if shape(text, module) == ('special', 'AtomicName') and (name == 'StructObj' or n == 'struct_name' or n == 'template_name'):
                method = 'reference_template_name' if n == 'template_name' else 'reference_struct_name'
                lines.append(f'    graph.{method}(&value.{n}, runtime, locals, refs, outputs);')
                continue
            lines.extend(field_source(shape(text, module), n, f'&value.{n}', module, 4))
            lines.extend(emit(shape(text, module), f'&value.{n}', 4))
    else:
        lines.append('    match value {')
        for vname, vkind, group in fields:
            # Failed evidence never establishes graph dependencies or outputs.
            rejected = vname.startswith('Fail') or vname in ('NotFound', 'Unknown', 'Unsupported')
            bindings = [f'p{i}' for i in range(len(group))]
            path = aliases[full] + '::' + vname
            if vkind == 'tuple':
                pattern = path + '(' + ', '.join('_' if rejected else b for b in bindings) + ')'
            elif vkind == 'named':
                pattern = path + ' { ' + ( '..' if rejected else ', '.join(n + ': ' + b for (n, _), b in zip(group, bindings))) + ' }'
            else:
                pattern = path
            lines.append('        ' + pattern + ' => {')
            if not rejected:
                for (_, text), binding in zip(group, bindings):
                    lines.extend(field_source(shape(text, module), _, binding, module, 12))
                    lines.extend(emit(shape(text, module), binding, 12))
            lines.append('        }')
        lines.append('    }')
    lines += ['}', '']

destination = ROOT / 'src/graph/walk_generated.rs'
output = '\n'.join(lines)
if '--check' in sys.argv:
    if not destination.exists() or destination.read_text() != output:
        raise SystemExit('graph visitor is stale; run src/graph/generate_walk.py')
else:
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(output)
print(f'{len(selected)} typed visitors; {len(lines)} lines')
