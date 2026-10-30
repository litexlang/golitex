#!/usr/bin/env python3
"""Embed the bilingual source-owned glossary into the shared offline reader."""
import argparse
import json
from pathlib import Path
from audit_language_reference import ast_shapes, builtin_theorem_contracts

HERE = Path(__file__).resolve().parent
BEGIN = '  // BEGIN GENERATED LANGUAGE REFERENCE'
END = '  // END GENERATED LANGUAGE REFERENCE'

def validate(data):
    assert data['schema_version'] == 1
    expected = {key.split('.')[-1] for key in ast_shapes()['Stmt']}
    assert set(data['statements']) == expected, {'missing': sorted(expected-set(data['statements'])), 'stale': sorted(set(data['statements'])-expected)}
    shapes = ast_shapes()
    for root in ['Obj', 'Fact']:
        assert set(data['ast_surfaces'][root]) == set(shapes[root]), ('AST inventory is stale', root)
    contracts=builtin_theorem_contracts()
    assert set(data.get('builtin_theorems',{})).issubset(contracts),'unknown native theorem identity'
    for group in ['entries', 'statements','builtin_theorems']:
        for key, card in data.get(group,{}).items():
            if group == 'entries' and 'statement' in card:
                assert set(card) == {'statement'} and card['statement'] in expected, key
                continue
            if group == 'entries' and 'reference' in card:
                assert set(card) <= {'reference','syntax','role'}, key
                target=data['entries'].get(card['reference'])
                assert target and 'reference' not in target and 'statement' not in target, (key,'invalid or chained reference')
                if 'syntax' in card:
                    assert isinstance(card['syntax'],str) and card['syntax'].strip(),key
                if 'role' in card:
                    assert card['role'] in ['operator','keyword','type'],key
                continue
            assert card.get('syntax'), key
            if group=='builtin_theorems':
                name=contracts[key]['name']
                assert card['syntax'].startswith(name+'(') and card['syntax'].endswith(')'),(key,'canonical theorem signature')
                params=card['syntax'][len(name)+1:-1].strip()
                assert (len(params.split(',')) if params else 0)==contracts[key]['arity'],(key,'theorem arity')
            if 'example' in card:
                assert isinstance(card['example'],str) and card['example'].strip(),key
            if 'role' in card:
                assert card['role'] in ['operator', 'keyword', 'type'], (key, 'role')
            for field in ['kind', 'summary', 'notes']:
                assert set(card[field]) == {'en', 'zh'}, (key, field)
                assert all(isinstance(value, str) and value.strip() for value in card[field].values()), (key, field)
    # These operations take explicit domain/codomain arguments. Catch accidental
    # regressions to the familiar but unsupported one-argument notation.
    for key in ['injective', 'surjective', 'bijective']:
        assert data['entries'][key]['syntax'] == '$'+key+'(A, B, f)', key
    assert 'd divides' in data['entries']['dvd']['summary']['en']
    return data

def resolved_entries(data):
    """Resolve source-only spelling references before embedding plain cards."""
    cards={}
    for key,card in data['entries'].items():
        if 'statement' in card:
            cards[key]=data['statements'][card['statement']]
        elif 'reference' in card:
            cards[key]={**data['entries'][card['reference']],**{field:value for field,value in card.items() if field!='reference'}}
        else:
            cards[key]=card
    return cards

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    data = validate(json.loads((HERE/'language_reference.json').read_text()))
    # Audit associations stay in the source catalogue, outside the browser.
    embedded = {'entries':resolved_entries(data), 'statements':data['statements'],'builtin_theorems':data.get('builtin_theorems',{})}
    generated = BEGIN+'\n  const languageReference='+json.dumps(embedded,ensure_ascii=False,separators=(',', ':'))+';\n'+END
    path=HERE/'web/reader.js';source=path.read_text()
    if BEGIN in source:
        start,end=source.index(BEGIN),source.index(END)+len(END)
        updated=source[:start]+generated+source[end:]
    else:
        anchor='\n  function mountReadingReader('
        assert anchor in source
        updated=source.replace(anchor,'\n'+generated+'\n'+anchor,1)
    if args.check:
        assert updated==source,'Reading language reference is stale; run python3 src/reading/generate_language_reference.py'
    else:path.write_text(updated)
    print(f"{len(data['statements'])} statement cards, {len(data['entries'])} surface cards, {len(data.get('builtin_theorems',{}))} builtin theorem cards; bilingual data valid")

if __name__=='__main__':main()
