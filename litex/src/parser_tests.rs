// #[cfg(test)]
// mod tests {
//     use crate::atom::{Atom, AtomWithModName, AtomWithoutModName};
//     use crate::atomic_fact::{
//         AtomicFact, EqualFact, GreaterEqualFact, IsCartFact, IsFiniteSetFact, IsNonemptySetFact,
//         IsSetFact, LessEqualFact, NormalAtomicFact, NotEqualFact, NotGreaterEqualFact,
//         NotIsCartFact, NotIsFiniteSetFact, NotIsNonemptySetFact, NotIsSetFact, NotLessEqualFact,
//     };
//     use crate::definition_stmt::{
//         DefLetStmt, DefPropStmt, DefSetTemplateStmt, DefStmt, HaveExistObjStmt,
//         HaveFnEqualCaseByCaseStmt, HaveFnEqualStmt, HaveObjEqualStmt,
//         HaveObjInNonemptySetOrParamTypeStmt,
//     };
//     use crate::eval_stmt::EvalStmt;
//     use crate::exist_fact::{ExistFact, TrueExistFact};
//     use crate::fact::Fact;
//     use crate::forall_fact::ForallFact;
//     use crate::forall_fact_with_iff::ForallFactWithIff;
//     use crate::know_stmt::KnowStmt;
//     use crate::obj::{
//         Add, Cap, Cart, CartDim, Choose, ClosedRange, Count, Cup, Dim, DisjointUnion, Div, FnObj,
//         FnSetWithDom, FnSetWithoutDom, InstSetTemplateObj, Intersect, ListSet, Mod, Mul, NObj,
//         NPosObj, Number, Obj, ObjAtIndex, Pow, PowerSet, Proj, QNeg, QNz, QObj, QPos, Range, RNeg,
//         RNz, RObj, RPos, SetBuilder, SetMinus, Sub, Tuple, Union, Val, ZNeg, ZNz, ZObj, ZPos,
//     };
//     use crate::or_fact::OrFact;
//     use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
//     use crate::parameter_type_and_property::{
//         ParamDefWithParamSet, ParamDefWithParamType, ParamDefWithParamTypeOrProperty, ParamType,
//         Set,
//     };
//     use crate::parser::Parser;
//     use crate::proof_technique_stmt::{
//         ClosedRangeOrRange, ProveByContradictionStmt, ProveByEnumerationStmt, ProveByEqualSetStmt,
//         ProveByInductionStmt, ProveCaseByCaseStmt, ProveForStmt, ProofTechniqueStmt,
//         ViewFnAsSetStmt,
//     };
//     use crate::prove_stmt::ProveStmt;
//     use crate::specific_fact::SpecFact;
//     use crate::stmt::Stmt;
//     use crate::token_block::TokenBlock;
//     use crate::tokenizer::tokenize_line;
//     use crate::tooling_stmt::{
//         ClearStmt, DoNothingStmt, ImportGlobalModuleStmt, ImportRelativePathStmt, ImportStmt,
//         RunFileStmt, ToolingStmt,
//     };
//     use crate::witness_stmt::{WitnessExistFact, WitnessNonemptySet, WitnessStmt};

//     fn tb_from_line(line: &str) -> TokenBlock {
//         TokenBlock::new(tokenize_line(line), vec![], (1, 0))
//     }

//     fn parse_obj_str(s: &str) -> Obj {
//         let mut tb = tb_from_line(s);
//         Parser::new().obj(&mut tb).expect("parse obj failed")
//     }

//     fn parse_fact_str(s: &str) -> Fact {
//         let mut tb = tb_from_line(s);
//         Parser::new().fact(&mut tb).expect("parse fact failed")
//     }

//     fn parse_stmt_blocks(s: &str) -> Vec<Stmt> {
//         let blocks = TokenBlock::parse_blocks(s, 0).expect("parse blocks failed");
//         let parser = Parser::new();
//         let mut out = Vec::new();
//         for mut b in blocks {
//             out.push(parser.stmt(&mut b).expect("parse stmt failed"));
//         }
//         out
//     }

//     fn roundtrip_fact(fact: Fact) {
//         let s = format!("{}", fact);
//         let parsed = parse_fact_str(&s);
//         assert_eq!(format!("{}", parsed), s);
//     }

//     fn roundtrip_stmt(stmt: Stmt) {
//         let s = format!("{}", stmt);
//         // stmt 需要通过带缩进的文本来解析，因此用一个单独的 block
//         let parsed_list = parse_stmt_blocks(&s);
//         assert_eq!(parsed_list.len(), 1);
//         assert_eq!(format!("{}", parsed_list[0]), s);
//     }

//     fn simple_atom(name: &str) -> Obj {
//         Obj::AtomWithoutModName(AtomWithoutModName::new(name))
//     }

//     fn sample_facts() -> Vec<Fact> {
//         let obj_a = simple_atom("a");
//         let obj_b = simple_atom("b");

//         // Atomic facts
//         let eq = AtomicFact::EqualFact(EqualFact::new(obj_a.clone(), obj_b.clone(), None));
//         let le = AtomicFact::LessEqualFact(LessEqualFact::new(obj_a.clone(), obj_b.clone(), None));
//         let ge = AtomicFact::GreaterEqualFact(GreaterEqualFact::new(obj_a.clone(), obj_b.clone(), None));
//         let is_set = AtomicFact::IsSetFact(IsSetFact::new(simple_atom("S"), None));
//         let not_eq = AtomicFact::NotEqualFact(NotEqualFact::new(obj_a.clone(), obj_b.clone(), None));
//         let not_le =
//             AtomicFact::NotLessEqualFact(NotLessEqualFact::new(obj_a.clone(), obj_b.clone(), None));
//         let not_ge = AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact::new(
//             obj_a.clone(),
//             obj_b.clone(),
//             None,
//         ));
//         let is_cart = AtomicFact::IsCartFact(IsCartFact::new(simple_atom("S"), None));
//         let not_is_cart = AtomicFact::NotIsCartFact(NotIsCartFact::new(simple_atom("S"), None));
//         let is_nonempty =
//             AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(simple_atom("S"), None));
//         let not_is_nonempty =
//             AtomicFact::NotIsNonemptySetFact(NotIsNonemptySetFact::new(simple_atom("S"), None));
//         let is_finite = AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(simple_atom("S"), None));
//         let not_is_finite =
//             AtomicFact::NotIsFiniteSetFact(NotIsFiniteSetFact::new(simple_atom("S"), None));

//         let atomic_examples = vec![
//             eq,
//             le,
//             ge,
//             is_set,
//             not_eq,
//             not_le,
//             not_ge,
//             is_cart,
//             not_is_cart,
//             is_nonempty,
//             not_is_nonempty,
//             is_finite,
//             not_is_finite,
//         ];

//         let atomic_fact = Fact::AtomicFact(atomic_examples[0].clone());

//         // ExistFact
//         let params =
//             vec![ParamDefWithParamTypeOrProperty::ParamAndItsTypePair("x".to_string(), ParamType::Set(Set::new()))];
//         let or_fact = OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(
//             atomic_examples[0].clone(),
//         ));
//         let true_exist = ExistFact::TrueExistFact(TrueExistFact::new(params.clone(), vec![or_fact.clone()], None));

//         let exist_fact = Fact::ExistFact(true_exist.clone());

//         // OrFact
//         use crate::and_fact_or_specific_fact::AndFactOrSpecFact;
//         let spec1 = AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(
//             atomic_examples[0].clone(),
//         ));
//         let spec2 = AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(
//             atomic_examples[1].clone(),
//         ));
//         let or_fact_node = OrFact::new(vec![spec1, spec2], None);
//         let or_fact_fact = Fact::OrFact(or_fact_node);

//         // AndFact (AndSpecFacts)
//         use crate::and_fact::{AndFact, AndSpecFacts};
//         let and_spec_facts = AndSpecFacts::new(
//             vec![
//                 SpecFact::AtomicFact(atomic_examples[0].clone()),
//                 SpecFact::AtomicFact(atomic_examples[1].clone()),
//             ],
//             None,
//         );
//         let and_fact = Fact::AndFact(AndFact::AndSpecFacts(and_spec_facts));

//         // ForallFact
//         let forall_for_fact = ForallFact::new(
//             params.clone(),
//             vec![or_fact.clone()],
//             vec![or_fact.clone()],
//             None,
//         );
//         let forall_fact = Fact::ForallFact(forall_for_fact);

//         // ForallFactWithIff 使用另一个独立的 ForallFact
//         let forall_for_iff = ForallFact::new(
//             params,
//             vec![or_fact.clone()],
//             vec![or_fact],
//             None,
//         );
//         let forall_with_iff =
//             ForallFactWithIff::new(forall_for_iff, vec![OrFactOrAndFactOrSpecFact::SpecFact(
//                 SpecFact::AtomicFact(atomic_examples[0].clone()),
//             )], None);
//         let forall_with_iff_fact = Fact::ForallFactWithIff(forall_with_iff);

//         vec![
//             atomic_fact,
//             exist_fact,
//             or_fact_fact,
//             and_fact,
//             forall_fact,
//             forall_with_iff_fact,
//         ]
//     }

//     fn sample_stmts() -> Vec<Stmt> {
//         let obj_a = simple_atom("a");
//         let obj_b = simple_atom("b");

//         let atomic = AtomicFact::EqualFact(EqualFact::new(obj_a.clone(), obj_b.clone(), None));
//         let fact = Fact::AtomicFact(atomic.clone());

//         // Stmt::Fact
//         let fact_stmt = Stmt::Fact(Fact::AtomicFact(atomic.clone()));

//         // DefStmt::DefLetStmt
//         let def_let = DefLetStmt::new(
//             vec![ParamDefWithParamType::ParamAndItsTypePair(
//                 "x".to_string(),
//                 ParamType::Set(Set::new()),
//             )],
//             vec![fact],
//             None,
//         );
//         let def_let_stmt = Stmt::DefStmt(DefStmt::DefLetStmt(def_let));

//         // DefStmt::DefPropStmt
//         let def_prop = DefPropStmt::new(
//             "P".to_string(),
//             vec![ParamDefWithParamTypeOrProperty::ParamAndItsTypePair(
//                 "x".to_string(),
//                 ParamType::Set(Set::new()),
//             )],
//             Some(vec![Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
//                 obj_a.clone(),
//                 obj_b.clone(),
//                 None,
//             )))]),
//             None,
//         );
//         let def_prop_stmt = Stmt::DefStmt(DefStmt::DefPropStmt(def_prop));

//         // DefStmt::HaveObjInNonemptySetStmt
//         let have_in_set = HaveObjInNonemptySetOrParamTypeStmt::new(
//             vec![ParamDefWithParamType::ParamAndItsTypePair(
//                 "x".to_string(),
//                 ParamType::Set(Set::new()),
//             )],
//             None,
//         );
//         let have_in_set_stmt = Stmt::DefStmt(DefStmt::HaveObjInNonemptySetStmt(have_in_set));

//         // DefStmt::HaveObjEqualStmt
//         let have_equal = HaveObjEqualStmt::new(
//             vec![ParamDefWithParamType::ParamAndItsTypePair(
//                 "x".to_string(),
//                 ParamType::Set(Set::new()),
//             )],
//             vec![obj_a.clone()],
//             None,
//         );
//         let have_equal_stmt = Stmt::DefStmt(DefStmt::HaveObjEqualStmt(have_equal));

//         // DefStmt::HaveExistObjStmt
//         let params = vec![ParamDefWithParamTypeOrProperty::ParamAndItsTypePair(
//             "x".to_string(),
//             ParamType::Set(Set::new()),
//         )];
//         let facts_for_exist = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(
//             atomic.clone(),
//         ))];
//         let true_exist = TrueExistFact::new(params.clone(), facts_for_exist.clone(), None);
//         let have_exist = HaveExistObjStmt::new(true_exist, None);
//         let have_exist_stmt = Stmt::DefStmt(DefStmt::HaveExistObjStmt(have_exist));

//         // DefStmt::HaveFnEqualStmt
//         let fn_set = FnSetWithDom::new(
//             vec![ParamDefWithParamSet::ParamAndItsSetPair(
//                 "x".to_string(),
//                 obj_a.clone(),
//             )],
//             facts_for_exist.clone(),
//             obj_b.clone(),
//         );
//         let have_fn_eq =
//             HaveFnEqualStmt::new("f".to_string(), fn_set.clone(), obj_b.clone(), None);
//         let have_fn_eq_stmt = Stmt::DefStmt(DefStmt::HaveFnEqualStmt(have_fn_eq));

//         // DefStmt::HaveFnEqualCaseByCaseStmt
//         let case_fact =
//             crate::and_fact_or_specific_fact::AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(
//                 atomic.clone(),
//             ));
//         let have_fn_case = HaveFnEqualCaseByCaseStmt::new(
//             "f".to_string(),
//             fn_set,
//             vec![case_fact],
//             vec![obj_b.clone()],
//             None,
//         );
//         let have_fn_case_stmt = Stmt::DefStmt(DefStmt::HaveFnEqualCaseByCaseStmt(have_fn_case));

//         // DefStmt::DefSetTemplateStmt
//         let set_template = DefSetTemplateStmt::new(
//             "T".to_string(),
//             vec![ParamDefWithParamTypeOrProperty::ParamAndItsTypePair(
//                 "x".to_string(),
//                 ParamType::Set(Set::new()),
//             )],
//             vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(
//                 atomic.clone(),
//             ))],
//             obj_a.clone(),
//             None,
//         );
//         let def_set_template_stmt =
//             Stmt::DefStmt(DefStmt::DefSetTemplateStmt(set_template));

//         // ClaimStmt
//         use crate::claim_stmt::ClaimStmt;
//         let claim = ClaimStmt::new(Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
//             obj_a.clone(),
//             obj_b.clone(),
//             None,
//         ))), vec![], None);
//         let claim_stmt = Stmt::ClaimStmt(claim);

//         // KnowStmt
//         let know = KnowStmt::new(vec![Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
//             obj_a.clone(),
//             obj_b.clone(),
//             None,
//         )))], None);
//         let know_stmt = Stmt::KnowStmt(know);

//         // ProveStmt
//         let prove = ProveStmt::new(vec![fact_stmt], None);
//         let prove_stmt = Stmt::ProveStmt(prove);

//         // ToolingStmt::Import, Clear, DoNothing, RunFile
//         let import_rel = ImportStmt::ImportRelativePath(ImportRelativePathStmt::new(
//             "./demo.lt",
//             None,
//             None,
//         ));
//         let tooling_import = Stmt::ToolingStmt(ToolingStmt::Import(import_rel));

//         let clear = ClearStmt::new(None);
//         let tooling_clear = Stmt::ToolingStmt(ToolingStmt::Clear(clear));

//         let do_nothing = DoNothingStmt::new(None);
//         let tooling_do_nothing = Stmt::ToolingStmt(ToolingStmt::DoNothing(do_nothing));

//         let run_file = RunFileStmt::new("./demo.lt", None);
//         let tooling_run_file = Stmt::ToolingStmt(ToolingStmt::RunFile(run_file));

//         // EvalStmt
//         let eval = EvalStmt::new(obj_a.clone(), None);
//         let eval_stmt = Stmt::EvalStmt(eval);

//         // WitnessStmt
//         let witness_exist = WitnessExistFact::new(
//             vec![obj_a.clone()],
//             TrueExistFact::new(
//                 vec![ParamDefWithParamTypeOrProperty::ParamAndItsTypePair(
//                     "x".to_string(),
//                     ParamType::Set(Set::new()),
//                 )],
//                 vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(
//                     AtomicFact::EqualFact(EqualFact::new(obj_a.clone(), obj_b.clone(), None)),
//                 ))],
//                 None,
//             ),
//             vec![Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(
//                 EqualFact::new(obj_a.clone(), obj_b.clone(), None),
//             )))],
//             None,
//         );
//         let witness_exist_stmt =
//             Stmt::WitnessStmt(WitnessStmt::WitnessExistFact(witness_exist));

//         let witness_nonempty =
//             WitnessNonemptySet::new(obj_a.clone(), obj_b.clone(), vec![Stmt::Fact(Fact::AtomicFact(
//                 AtomicFact::EqualFact(EqualFact::new(obj_a.clone(), obj_b.clone(), None)),
//             ))], None);
//         let witness_nonempty_stmt =
//             Stmt::WitnessStmt(WitnessStmt::WitnessNonemptySet(witness_nonempty));

//         // ProofTechniqueStmt variants
//         let prove_case = ProveCaseByCaseStmt::new(
//             vec![crate::and_fact_or_specific_fact::AndFactOrSpecFact::SpecFact(
//                 SpecFact::AtomicFact(atomic.clone()),
//             )],
//             vec![Fact::AtomicFact(atomic.clone())],
//             vec![vec![Stmt::Fact(Fact::AtomicFact(atomic.clone()))]],
//             vec![None],
//             None,
//         );
//         let prove_case_stmt =
//             Stmt::ProofTechnique(ProofTechniqueStmt::ProveCaseByCase(prove_case));

//         let prove_contra = ProveByContradictionStmt::new(
//             Fact::AtomicFact(atomic.clone()),
//             vec![Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(
//                 EqualFact::new(obj_a.clone(), obj_b.clone(), None),
//             )))],
//             OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(atomic.clone())),
//             None,
//         );
//         let prove_contra_stmt =
//             Stmt::ProofTechnique(ProofTechniqueStmt::ProveByContradiction(prove_contra));

//         let prove_enum = ProveByEnumerationStmt::new(
//             vec!["x".to_string()],
//             vec![obj_a.clone()],
//             vec![Fact::AtomicFact(atomic.clone())],
//             vec![Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(
//                 EqualFact::new(obj_a.clone(), obj_b.clone(), None),
//             )))],
//             None,
//         );
//         let prove_enum_stmt =
//             Stmt::ProofTechnique(ProofTechniqueStmt::ProveByEnumeration(prove_enum));

//         let prove_induc = ProveByInductionStmt::new(
//             vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(
//                 atomic.clone(),
//             ))],
//             "n".to_string(),
//             vec![Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(
//                 EqualFact::new(obj_a.clone(), obj_b.clone(), None),
//             )))],
//             obj_a.clone(),
//             None,
//         );
//         let prove_induc_stmt =
//             Stmt::ProofTechnique(ProofTechniqueStmt::ProveByInduction(prove_induc));

//         let prove_for = ProveForStmt::new(
//             vec!["n".to_string()],
//             vec![ClosedRangeOrRange::Range(Range {
//                 start: Box::new(simple_atom("0")),
//                 end: Box::new(simple_atom("10")),
//             })],
//             vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(
//                 atomic.clone(),
//             ))],
//             vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(
//                 atomic.clone(),
//             ))],
//             vec![Stmt::Fact(Fact::AtomicFact(atomic.clone()))],
//             None,
//         );
//         let prove_for_stmt =
//             Stmt::ProofTechnique(ProofTechniqueStmt::ProveForStmt(prove_for));

//         let prove_eq_set =
//             ProveByEqualSetStmt::new(
//                 obj_a.clone(),
//                 obj_b.clone(),
//                 vec![Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(
//                     EqualFact::new(obj_a.clone(), obj_b.clone(), None),
//                 )))],
//                 None,
//             );
//         let prove_eq_set_stmt =
//             Stmt::ProofTechnique(ProofTechniqueStmt::ProveByEqualSet(prove_eq_set));

//         let view_fn_as_set =
//             ViewFnAsSetStmt::new(simple_atom("f"), None);
//         let view_fn_as_set_stmt =
//             Stmt::ProofTechnique(ProofTechniqueStmt::ViewFnAsSet(view_fn_as_set));

//         // ProveStmt itself already covered; also add a simple Stmt::Fact again for completeness.

//         vec![
//             Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
//                 obj_a,
//                 obj_b,
//                 None,
//             )))),
//             def_let_stmt,
//             def_prop_stmt,
//             have_in_set_stmt,
//             have_equal_stmt,
//             have_exist_stmt,
//             have_fn_eq_stmt,
//             have_fn_case_stmt,
//             def_set_template_stmt,
//             claim_stmt,
//             know_stmt,
//             prove_stmt,
//             tooling_import,
//             tooling_clear,
//             tooling_do_nothing,
//             tooling_run_file,
//             eval_stmt,
//             witness_exist_stmt,
//             witness_nonempty_stmt,
//             prove_case_stmt,
//             prove_contra_stmt,
//             prove_enum_stmt,
//             prove_induc_stmt,
//             prove_for_stmt,
//             prove_eq_set_stmt,
//             view_fn_as_set_stmt,
//         ]
//     }

//     #[test]
//     #[ignore]
//     fn parse_all_fact_variants_roundtrip() {
//         for fact in sample_facts() {
//             roundtrip_fact(fact);
//         }
//     }

//     #[test]
//     #[ignore]
//     fn parse_all_stmt_variants_roundtrip() {
//         for stmt in sample_stmts() {
//             roundtrip_stmt(stmt);
//         }
//     }
// }

