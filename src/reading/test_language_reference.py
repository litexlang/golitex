#!/usr/bin/env python3
"""Catalogue structure/identity controls; public hover checks live in web/tests."""
import copy
import json
from pathlib import Path
import unittest
import re
from generate_language_reference import validate, resolved_entries, resolved_builtin_theorems
from audit_language_reference import ast_shapes, audit, native_unicode_aliases, builtin_theorem_inventory, builtin_theorem_contracts
from generate_highlighting import catalogue, delegated_spellings

class LanguageReferenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data=json.loads((Path(__file__).parent/'language_reference.json').read_text())
    def test_live_statement_and_mathematical_inventory(self):
        validate(self.data)
        shapes=ast_shapes()
        self.assertEqual(set(self.data['statements']),{key.split('.')[-1] for key in shapes['Stmt']})
        for root in ['Obj','Fact']:
            self.assertEqual(set(self.data['ast_surfaces'][root]),set(shapes[root]))
    def test_missing_language_does_not_count_as_complete(self):
        data=copy.deepcopy(self.data);del data['statements']['ByThmStmt']['notes']['zh']
        with self.assertRaises(AssertionError):validate(data)
    def test_domain_arguments_cannot_disappear(self):
        for name in ['injective','surjective','bijective']:
            data=copy.deepcopy(self.data);data['entries'][name]['syntax']='$'+name+'(f)'
            with self.assertRaises(AssertionError):validate(data)
    def test_builtin_predicate_domains_match_current_interface(self):
        self.assertIn('d ≠ 0',self.data['entries']['dvd']['notes']['zh'])
        self.assertIn('a,b ∈ ℕ',self.data['entries']['coprime']['notes']['zh'])
        self.assertIn('p ∈ ℕ',self.data['entries']['prime']['notes']['zh'])
    def test_new_statement_requires_authored_entry(self):
        data=copy.deepcopy(self.data);del data['statements']['ByCasesStmt']
        with self.assertRaises(AssertionError):validate(data)
    def test_compound_and_statement_help_share_one_author(self):
        self.assertEqual(self.data['entries']['by thm'],{'statement':'ByThmStmt'})
        data=copy.deepcopy(self.data);data['entries']['by thm']={'statement':'UnknownStatement'}
        with self.assertRaises(AssertionError):validate(data)
    def test_retired_predicates_remain_explicitly_retired(self):
        for name in ['is_cart','is_tuple','fn_eq','fn_eq_in']:
            self.assertEqual(self.data['entries'][name]['status'],'removed')
        for name in ['cart_dim','tuple_dim','proj']:
            self.assertEqual(self.data['entries'][name]['status'],'removed')
        self.assertEqual(self.data['entries']['as']['status'],'reserved')
        self.assertEqual(self.data['entries']['import']['status'],'not_statement')
    def test_unknown_surfaces_and_generic_help_are_not_complete(self):
        report=audit()
        for root in ['Obj','Fact']:
            incomplete=[item for item in report['mathematical_help'][root]['branches'] if not item['surface']]
            self.assertTrue(incomplete)
            self.assertTrue(all(item['coverage']=='surface_unresolved_or_contextual' for item in incomplete))
        for category in report['lexical'].values():
            self.assertEqual(category['total'],category['reference_cards']+category['brief_only']+category['generic_or_missing'])
    def test_range_and_aggregate_endpoint_contracts(self):
        self.assertIn('a ≤ k < b',self.data['entries']['range']['notes']['en'])
        self.assertIn('a ≤ k ≤ b',self.data['entries']['closed_range']['notes']['en'])
        for name in ['sum','product']:
            self.assertIn('a ≤ b',self.data['entries'][name]['notes']['en'])
            self.assertIn('Both endpoints',self.data['entries'][name]['notes']['en'])
        self.assertIn('If a>b',self.data['entries']['reduce']['notes']['en'])
    def test_matrix_conjugation_and_inverse_contracts(self):
        self.assertIn('conj(u(j))*v(j)',self.data['entries']['inner_product']['notes']['en'])
        self.assertIn('No conjugation',self.data['entries']['outer_product']['notes']['en'])
        self.assertIn('det(A,n) ≠ 0',self.data['entries']['matrix_inv']['notes']['en'])
        self.assertEqual(self.data['entries']['matrix_inv']['syntax'],'matrix_inv(A, n)')
        self.assertNotIn('matrix_inverse',self.data['entries'])
        self.assertIn('n−1,n−1',self.data['entries']['matrix_minor']['notes']['en'])
    def test_selectors_require_proofs_and_do_not_change_name_contracts(self):
        self.assertEqual(self.data['entries']['lim']['syntax'],'lim(a)')
        self.assertEqual(self.data['entries']['fn_lim']['syntax'],'fn_lim(f, x0)')
        for name in ['lim','limsup','liminf','fn_lim','derivative']:
            self.assertIn('proved',self.data['entries'][name]['notes']['en'])
        self.assertIn('not ±∞',self.data['entries']['sup']['notes']['en'])
    def test_documented_roles_are_not_arbitrary_css_classes(self):
        data=copy.deepcopy(self.data);data['entries']['sum']['role']='invented'
        with self.assertRaises(AssertionError):validate(data)
    def test_mapped_mathematical_surfaces_keep_their_semantic_cards(self):
        report=audit()
        for root in ['Obj','Fact']:
            self.assertEqual(report['mathematical_help'][root]['counts']['brief_or_missing'],0)
    def test_native_source_hint_keys_resolve_to_authored_cards(self):
        source=(Path(__file__).parent/'source_hints.rs').read_text()
        # Only the hint-key producer emits catalogue references. Token and
        # source-anchor checks elsewhere also use Some("...") for punctuation.
        producer=re.search(r'(?ms)^fn reference_key\b.*?^\}',source)
        self.assertIsNotNone(producer)
        keys=set(re.findall(r'Some\("([^"\n]+)"\)',producer.group()))
        self.assertTrue(keys)
        for key in keys:
            self.assertIn(key,self.data['entries'])
        self.assertEqual(self.data['entries']['obj:template']['syntax'],'\\Template<arguments>')
    def test_parser_delegated_math_names_are_in_the_inventory(self):
        groups=dict(catalogue())
        functions=delegated_spellings('ast/obj.rs','multivariable_selector_arity')
        predicates=delegated_spellings('ast/fact/atomic.rs','predicate_arity')
        self.assertIn('gradient_at',functions)
        self.assertIn('has_gradient_at',predicates)
        self.assertTrue(functions.issubset(groups['function']))
        self.assertTrue(predicates.issubset(groups['predicate']))
    def test_multivariable_cards_match_live_arities(self):
        root=Path(__file__).resolve().parents[1]
        for relative,method in [('ast/obj.rs','multivariable_selector_arity'),('ast/fact/atomic.rs','predicate_arity')]:
            source=(root/relative).read_text().split('pub fn '+method+'(',1)[1].split('\n    }',1)[0]
            arities=dict(re.findall(r'"([a-z_]+)"\s*=>\s*Some\((\d+)\)',source))
            self.assertTrue(arities)
            for name,arity in arities.items():
                card=self.data['entries'][name]
                self.assertEqual(len(card['syntax'].split('(',1)[1].rstrip(')').split(',')),int(arity),name)
                self.assertIn('Example:',card['notes']['en'])
                if relative=='ast/obj.rs':
                    self.assertIn('proved',card['notes']['en'])
    def test_multivariable_derivative_conventions_are_distinct(self):
        self.assertIn('matrix(R,m,n)',self.data['entries']['differential']['notes']['en'])
        self.assertEqual(self.data['entries']['curl']['syntax'],'curl(F, p)')
        self.assertIn('first in i and then in j',self.data['entries']['has_hessian_at']['notes']['en'])
        self.assertIn('does not guarantee total differentiability',self.data['entries']['has_gradient_at']['notes']['en'])
        self.assertIn('p need not belong to D',self.data['entries']['lim_multi_at']['notes']['en'])
    def test_infix_spellings_share_one_mathematical_owner(self):
        cards=resolved_entries(self.data)
        for spelling,name in [('∪','union'),('∩','intersect'),('×','cart'),('∘','compose')]:
            for field in ['kind','summary','notes']:
                self.assertEqual(cards[spelling][field],cards[name][field])
            self.assertEqual(cards[spelling]['role'],'operator')
        for target in ['absent','×','by def']:
            data=copy.deepcopy(self.data);data['entries']['∪']['reference']=target
            with self.assertRaises(AssertionError):validate(data)
    def test_unicode_normalization_is_separate_from_direct_cards(self):
        aliases=native_unicode_aliases()
        self.assertEqual(aliases['ℤ+'],['Z+'])
        self.assertEqual(aliases['∈'],['$','in'])
        self.assertEqual(aliases['⊂'],aliases['⊊'])
        types=audit()['lexical']['type']
        self.assertEqual(types['normalized_to']['ℝ+'],['R+'])
        self.assertEqual(types['normalized_reference_cards'],11)
        self.assertEqual(types['generic_or_missing'],0)
    def test_postfix_and_structural_symbols_keep_their_owners(self):
        cards=resolved_entries(self.data)
        for spelling,name in [('!','factorial'),('&','obj:struct_type'),('.','obj:field'),('\\','obj:template'),('...','closed_range')]:
            self.assertEqual(cards[spelling]['notes'],cards[name]['notes'])
        self.assertNotEqual(cards['!']['summary'],cards['exist!']['summary'])
        self.assertIn('0! = 1',cards['!']['notes']['en'])
        self.assertIn('nonintegers',cards['!']['notes']['en'])
    def test_generic_theorem_labels_do_not_count_as_explanations(self):
        report=builtin_theorem_inventory('function theoremReference(id){return {kind:"Builtin theorem",summary:"A theorem provided by Litex"};}')
        self.assertGreater(report['total'],0)
        self.assertEqual(report['counts']['dedicated_reference'],0)
        self.assertEqual(report['counts']['generic_or_missing'],report['total'])
        self.assertEqual(len(report['branches']),report['total'])
    def test_builtin_reference_identity_signature_and_language_guards(self):
        contracts=builtin_theorem_contracts()
        for identity,card in self.data['builtin_theorems'].items():
            self.assertTrue(card['syntax'].startswith(contracts[identity]['name']+'('))
            self.assertTrue(card['example'])
        for mode in ['identity','arity','name','language']:
            data=copy.deepcopy(self.data)
            if mode=='identity':data['builtin_theorems']['FutureTheorem']=data['builtin_theorems']['PrimeDivisor']
            if mode=='arity':data['builtin_theorems']['PrimeDivisor']['syntax']='prime_divisor(m, p)'
            if mode=='name':data['builtin_theorems']['PrimeDivisor']['syntax']='prime_divides_product(m)'
            if mode=='language':del data['builtin_theorems']['PrimeDivisor']['notes']['zh']
            with self.assertRaises(AssertionError):validate(data)
    def test_unwired_theorem_cards_do_not_inflate_coverage(self):
        cards=self.data['builtin_theorems']
        generic='function theoremReference(id){return null;}'
        self.assertEqual(builtin_theorem_inventory(generic,cards)['counts']['dedicated_reference'],0)
        source=(Path(__file__).parent/'web/reader.js').read_text()
        self.assertEqual(builtin_theorem_inventory(source,cards)['counts']['dedicated_reference'],len(cards))
        legacy=copy.deepcopy(self.data);del legacy['builtin_theorems'];validate(legacy)
    def test_theorem_declaration_keys_come_from_native_contracts(self):
        data=copy.deepcopy(self.data)
        data['builtin_theorems']['PrimeDivisor']['native_name']='forged_name'
        data['builtin_theorems']['PrimeDivisor']['native_arity']=19
        resolved=resolved_builtin_theorems(data)
        contracts=builtin_theorem_contracts()
        for key,card in resolved.items():
            self.assertEqual(card['native_name'],contracts[key]['name'])
            self.assertEqual(card['native_arity'],contracts[key]['arity'])
        self.assertEqual(resolved_builtin_theorems({}),{})

if __name__=='__main__':unittest.main()
