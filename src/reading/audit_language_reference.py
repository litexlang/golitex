#!/usr/bin/env python3
"""Inventory reading help separately from actual hover/proof-form acceptance.

Counts concern catalogue presence, not mathematical correctness, source anchoring
or proof coverage. AST sums flatten dispatch enums; IdentifierObj encodings are
one identifier form, and nested property-kind fields are not separate branches.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent

def module(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + '.py'))
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value

def catalogues(source):
    scanner = module('generate_capture')
    masked = scanner.clean(source)
    values = {}
    for name in ['statementTypes', 'syntaxHelp', 'syntaxPhrases', 'standardSetHelp',
                 'builtinObjectHelp', 'setOperatorHelp', 'keywordReference']:
        match = re.search(r'const ' + name + r'\s*=\s*\{', source)
        start = match.end() - 1
        literal = source[start:scanner.closing(masked, start) + 1]
        literals = [literal]
        for extra in re.finditer(r'Object\.assign\(' + name + r',\s*\{', source):
            begin = extra.end() - 1
            literals.append(source[begin:scanner.closing(masked, begin) + 1])
        values[name] = literals
    # Evaluate only these trusted repository data literals, never the component
    # or arbitrary user input. No private viewer hook or source rewrite is used.
    script = 'const vm=require("vm");let s="";process.stdin.on("data",b=>s+=b);process.stdin.on("end",()=>{const out={};for(const [k,vs] of Object.entries(JSON.parse(s)))out[k]=Object.assign({},...vs.map(v=>vm.runInNewContext("("+v+")",Object.create(null))));process.stdout.write(JSON.stringify(out));});'
    run = subprocess.run(['node', '-e', script], input=json.dumps(values), text=True,
                         capture_output=True, check=True)
    return json.loads(run.stdout)

def ast_shapes():
    records, _, _, _ = module('generate_capture').inventory()
    types = {record['name']: record for full, record in records.items()
             if full.startswith('crate::ast::')}
    def visit(name, path):
        result = []
        for variant, _, fields in types[name]['variants']:
            key = path + '.' + variant
            target = fields[0][1] if len(fields) == 1 else ''
            recurse = (target in types and types[target]['kind'] == 'enum'
                       and target != 'IdentifierObj'
                       and not (path == 'Stmt' and variant == 'Fact'))
            result.extend(visit(target, key) if recurse else [key])
        return result
    return {root: visit(root, root) for root in ['Stmt', 'Obj', 'Fact']}

def native_unicode_aliases():
    """Read the tokenizer's literal alias table, including named constants."""
    source=(HERE.parent/'tokenize/symbols.rs').read_text()
    constants={key:json.loads(value) for key,value in re.findall(r'pub const (\w+): &str = ("(?:[^"\\]|\\.)*");',source)}
    scanner=module('generate_capture');start=source.index('{',source.index('pub fn unicode_alias_tokens('))
    body=source[start:scanner.closing(scanner.clean(source),start)+1]
    term=r'"(?:[^"\\]|\\.)*"|[A-Z_]+'
    resolve=lambda value:json.loads(value) if value.startswith('"') else constants[value]
    aliases={}
    for left,right in re.findall(r'((?:'+term+r')(?:\s*\|\s*(?:'+term+r'))*)\s*=>\s*Some\(&\[([^\]]*)\]\)',body):
        tokens=[resolve(item) for item in re.findall(term,right)]
        for name in re.findall(term,left):aliases[resolve(name)]=tokens
    assert aliases.get('ℝ+')==['R+'] and aliases.get('∈')==['$','in']
    return aliases

def builtin_theorem_contracts():
    """Native identities, canonical public names and literal arity dispatch."""
    scanner=module('generate_capture')
    records,*_=scanner.inventory()
    record=records['crate::builtin_theorem::BuiltinTheoremId']
    source=(HERE.parent/'builtin_theorem.rs').read_text()
    names=dict(re.findall(r'Self::(\w+)\s*=>\s*(?:\{\s*)?"([a-z_][a-z_0-9]*)"',source))
    start=source.index('{',source.index('pub fn arity('))
    body=scanner.clean(source[start:scanner.closing(scanner.clean(source),start)+1])
    fallback=re.findall(r'_\s*=>\s*(\d+)',body)
    assert len(fallback)==1,'builtin theorem arity default needs explicit audit'
    arms=re.findall(r'((?:Self::\w+\s*(?:\|\s*)?)+)\s*=>\s*(\d+)',body)
    assert len(re.findall(r'=>',body))==len(arms)+1,'nonliteral builtin arity needs explicit audit'
    arities={variant:int(fallback[0]) for variant,_,_ in record['variants']}
    for arm,arity in arms:
        for variant in re.findall(r'Self::(\w+)',arm):
            assert variant in arities,variant
            arities[variant]=int(arity)
    assert set(arities).issubset(names),'native theorem names need explicit audit'
    return {variant:{'name':names[variant],'arity':arity} for variant,arity in arities.items()}

def builtin_theorem_inventory(reader_source, authored_cards=None):
    """Do not count a generic theorem label or an unwired card as an explanation."""
    scanner=module('generate_capture')
    contracts=builtin_theorem_contracts()
    body=''
    if 'function theoremReference(' in reader_source:
        start=reader_source.index('{',reader_source.index('function theoremReference('))
        body=reader_source[start:scanner.closing(scanner.clean(reader_source),start)+1]
    authored=set(re.findall(r'theorem\.variant\s*===\s*"(\w+)"',body))
    if re.search(r'referenceCard\(\s*"thm:"\s*\+\s*theorem\.variant\s*\)',body) and 'languageReference.builtin_theorems' in reader_source:
        authored.update(authored_cards or {})
    catalogue={row['variant']:row for row in json.loads((HERE/'rule_catalogue_generated.json').read_text()) if row['category']=='builtin_theorem'}
    branches=[]
    for variant,contract in contracts.items():
        labels=catalogue.get(variant,{}).get('labels',{})
        branches.append({'variant':variant,'surface':contract['name'],'arity':contract['arity'],
                         'name_hover':'dedicated_reference' if variant in authored else 'generic_or_missing',
                         'bilingual_catalogue_comment':all(bool(labels.get(locale,{}).get('message')) for locale in ['zh','en'])})
    return {'total':len(branches),
            'counts':{status:sum(row['name_hover']==status for row in branches) for status in ['dedicated_reference','generic_or_missing']},
            'bilingual_catalogue_comments':sum(row['bilingual_catalogue_comment'] for row in branches),
            'branches':branches}

def audit(baseline=False):
    source = subprocess.run(['git', 'show', 'HEAD:src/reading/web/reader.js'], cwd=HERE, capture_output=True, text=True, check=True).stdout if baseline else (HERE / 'web/reader.js').read_text()
    old = catalogues(source)
    path = HERE / 'language_reference.json'
    new = json.loads(path.read_text()) if path.exists() else {'entries': {}, 'statements': {}}
    if baseline:
        new = {**new, 'entries': {}, 'statements': {}}
    rich = set(old['builtinObjectHelp']) | set(old['setOperatorHelp']) | set(old['keywordReference']) | set(new['entries'])
    brief = set(old['syntaxHelp']) | set(old['syntaxPhrases']) | set(old['standardSetHelp'])
    aliases=native_unicode_aliases()
    lexical = {}
    for kind, tokens in module('generate_highlighting').catalogue():
        normalized={token:aliases[token] for token in tokens if token not in rich and token in aliases and all(part in rich for part in aliases[token])}
        full = [token for token in tokens if token in rich or token in normalized]
        short = [token for token in tokens if token not in full and token in brief]
        missing = [token for token in tokens if token not in full and token not in brief]
        removed = [token for token in tokens if new['entries'].get(token, {}).get('status') == 'removed']
        lexical[kind] = {'total': len(tokens), 'reference_cards': len(full),
                         'normalized_reference_cards':len(normalized),
                         'normalized_to':normalized,
                         'brief_only': len(short), 'generic_or_missing': len(missing),
                         'removed_spellings': removed,
                         'reserved_spellings': [token for token in tokens if new['entries'].get(token, {}).get('status') == 'reserved'],
                         'configuration_only': [token for token in tokens if new['entries'].get(token, {}).get('status') == 'not_statement'],
                         'missing': missing}
    shapes = ast_shapes()
    statements = []
    for key in shapes['Stmt']:
        leaf = key.split('.')[-1]
        shared = old['statementTypes'].get(leaf, [])
        syntax = shared[2] if len(shared) > 2 else None
        status = 'dedicated_reference' if leaf in new['statements'] else 'shared_reference' if syntax in rich else 'brief_or_label_only'
        statements.append({'ast': key, 'surface': syntax, 'coverage': status})
    mathematical = {}
    for root in ['Obj', 'Fact']:
        records = []
        for key in shapes[root]:
            tokens = new.get('ast_surfaces', {}).get(root, {}).get(key)
            status = 'surface_unresolved_or_contextual' if not tokens else 'reference_cards' if all(token in rich for token in tokens) else 'brief_or_missing'
            records.append({'ast': key, 'surface': tokens, 'coverage': status,
                            'missing_cards': [token for token in tokens or [] if token not in rich]})
        mathematical[root] = {'counts': {status: sum(row['coverage'] == status for row in records) for status in ['reference_cards', 'brief_or_missing', 'surface_unresolved_or_contextual']}, 'branches': records}
    return {'scope': 'Static authored-help inventory; does not establish hover wiring, mathematical correctness, or proof-form coverage.',
            'ast': {key: {'total': len(value), 'branches': value} for key, value in shapes.items()},
            'statements': statements,
            'statement_coverage': {status: sum(row['coverage'] == status for row in statements) for status in ['dedicated_reference', 'shared_reference', 'brief_or_label_only']},
            'mathematical_help': mathematical,
            'lexical': lexical,
            'builtin_theorems':builtin_theorem_inventory(source,new.get('builtin_theorems',{}) if not baseline else {}),
            'unicode_aliases_outside_lexical_inventory':{key:value for key,value in aliases.items() if key not in {token for _,tokens in module('generate_highlighting').catalogue() for token in tokens}},
            'additional_phrase_cards': sorted(key for key in new['entries'] if ' ' in key),
            'new_authored_entries': len(new['entries'])}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--baseline', action='store_true', help='Compare current AST associations against the help tables at Git HEAD.')
    args = parser.parse_args()
    report = audit(args.baseline)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'ast': {key: value['total'] for key, value in report['ast'].items()},
                      'statement_coverage': report['statement_coverage'],
                      'mathematical_help': {key: value['counts'] for key,value in report['mathematical_help'].items()},
                      'lexical': {key: {k:v for k,v in value.items() if k not in ['missing','normalized_to']} for key,value in report['lexical'].items()},
                      'builtin_theorems':{key:value for key,value in report['builtin_theorems'].items() if key!='branches'},
                      'unicode_aliases_outside_lexical_inventory':len(report['unicode_aliases_outside_lexical_inventory'])}, ensure_ascii=False, indent=2))

if __name__ == '__main__':
    main()
