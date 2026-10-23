#!/usr/bin/env python3
"""Refresh the viewer's lexical vocabulary from the live parser spellings.

Only presentation categories are authored here. Source boundaries still come
from Tokenizer and resolved symbols always take precedence in the viewer.
"""
import argparse
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
BEGIN = '  // BEGIN GENERATED LEXICAL KINDS'
END = '  // END GENERATED LEXICAL KINDS'


def catalogue():
    constants = {}
    for relative in ['parse/keywords.rs', 'parse/fact_prop.rs']:
        source = (ROOT / relative).read_text()
        for name, literal in re.findall(r'pub const (\w+): &str = ("(?:[^"\\]|\\.)*");', source):
            constants[name] = json.loads(literal)
    keywords = set('prop abstract_prop let have obtain claim thm axiom strategy sketch trust import eval witness struct template strong_induc release expand register by algo for fn cases case contra def induc impossible from as forall exist exist! not and or st enumerate extension fn_extension transitive symmetric reflexive zorn_lemma axiom_of_choice regularity_axiom replacement_axiom'.split())
    types = set('obj set nonempty_set finite_set matrix N Z Q R C N+ Z+ Q+ R+ Z- Q- R- Z* Q* R* C*'.split())
    predicates = set('in subset superset proper_subset proper_superset fn_eq fn_eq_in injective surjective bijective prime coprime dvd'.split())
    operators = set('= != < > <= >= + - * / % ^ => <=> ∘ ∪ ∩ × ! &'.split())
    constants_values = {'i', 'e', 'pi'}
    groups = {kind: set() for kind in ['keyword', 'predicate', 'function', 'type', 'constant', 'operator', 'punctuation']}
    for name, spelling in constants.items():
        if spelling in keywords or spelling == '?':
            kind = 'keyword'
        elif spelling == '$' or spelling in predicates or name.startswith(('IS_', 'HAS_')):
            kind = 'predicate'
        elif spelling in types:
            kind = 'type'
        elif spelling in constants_values:
            kind = 'constant'
        elif spelling in operators:
            kind = 'operator'
        elif re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', spelling):
            kind = 'function'
        else:
            kind = 'punctuation'
        groups[kind].add(spelling)
    # These predicates are deliberately enumerated by the parser's arity table.
    analysis = (ROOT / 'parse/real_analysis_fact.rs').read_text().split('impl Runtime', 1)[0]
    groups['predicate'].update(re.findall(r'"([a-z_]+)"', analysis))
    symbols = (ROOT / 'tokenize/symbols.rs').read_text().split('let mut symbols = vec![', 1)[1].split('];', 1)[0]
    known = set().union(*groups.values())
    for literal in re.findall(r'"(?:[^"\\]|\\.)*"', symbols):
        spelling = json.loads(literal)
        if spelling not in known:
            if spelling == '∉':
                kind = 'predicate'
            elif spelling[0] in 'ℕℤℚℝℂ':
                kind = 'type'
            elif any(char in spelling for char in '+-*/^'):
                kind = 'operator'
            else:
                kind = 'punctuation'
            groups[kind].add(spelling)
    primary = (ROOT / 'parse/object/primary.rs').read_text()
    for spelling in ['integral', 'derivative']:
        if f'"{spelling}"' in primary:
            groups['function'].add(spelling)
    return [[kind, sorted(tokens)] for kind, tokens in groups.items()]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    groups = catalogue()
    generated = BEGIN + '\n  const lexicalKinds=new Map(' + json.dumps(groups, ensure_ascii=False, separators=(',', ':')) + '.flatMap(([kind,tokens])=>tokens.map(token=>[token,kind])));\n' + END
    path = HERE / 'web/reader.js'
    source = path.read_text()
    if BEGIN in source:
        start, end = source.index(BEGIN), source.index(END) + len(END)
        updated = source[:start] + generated + source[end:]
    else:
        anchor = '  const standardSetHelp='
        updated = source.replace(anchor, generated + '\n' + anchor)
    if args.check:
        if source != updated:
            raise SystemExit('Reading lexical kinds are stale; run python3 src/reading/generate_highlighting.py')
    else:
        path.write_text(updated)
    print(f'{sum(len(tokens) for _, tokens in groups)} parser spellings in {len(groups)} presentation groups')


if __name__ == '__main__':
    main()
