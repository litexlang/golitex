use std::collections::HashMap;
mod verify;
use verify::VerifyState;
use verify::SyntacticVerifier;
mod simplify_polynomial;
mod common;
mod error;
use error::{ArithmeticError, NewAtomicFactError, StoreFactError, StmtError, ParseBlockError, ExecError, WellDefinedError};
use error::ParsingError;
mod execute;
use execute::Executor;
mod obj;
use obj::{QPos, ZPos, RPos, QNeg, ZNeg, RNeg, QNz, ZNz, RNz};
use obj::{
    Obj, FnObj, Number, Add, Sub, Mul, Div, Mod, Pow,
    Union, Intersect, SetMinus, SetDiff, Cup, Cap,
    ListSet, SetBuilder, FnSetWithoutDom, FnSetWithDom,
    NPosObj, NObj, QObj, ZObj, RObj, InstStructObj,
    Cart, CartDim, Proj, Dim, Tuple, Count, Range, ClosedRange, Val, PowerSet, Choose, ObjAtIndex,
    FnSetObj,
};
use obj::{Identifier, IdentifierWithMod, IdentifierOrIdentifierWithMod};
mod stmt;
use stmt::Stmt;
use stmt::definition_stmt::{DefStmt, DefStructStmt, HaveObjInNonemptySetOrParamTypeStmt, HaveObjEqualStmt, HaveExistObjStmt, HaveFnEqualStmt, HaveFnEqualCaseByCaseStmt, DefStructWithNoFieldStmt, DefStructWithFieldsStmt, DefPropStmt, DefLetStmt};
use stmt::claim_stmt::ClaimStmt;
use stmt::know_stmt::KnowStmt;
use stmt::proof_technique_stmt::{ProveCaseByCaseStmt, ProveByContradictionStmt, ProofTechniqueStmt, ProveByEnumerationStmt, ProveByInductionStmt, ProveForStmt, ClosedRangeOrRange, ProveByEqualSetStmt, ViewFnAsSetStmt};
use stmt::prove_stmt::ProveStmt;
use stmt::tooling_stmt::{ToolingStmt, ImportStmt, ImportRelativePathStmt, ImportGlobalModuleStmt, ClearStmt, DoNothingStmt, RunFileStmt};
use stmt::eval_stmt::EvalStmt;
use stmt::witness_stmt::{WitnessStmt, WitnessExistFact, WitnessNonemptySet};
use stmt::define_algorithm_stmt::{DefAlgoStmt, AlgoReturn, AlgoIf, AlgoReturnOrAlgoIf};
use stmt::parameter_type_and_property::{ParamType, Set, NonemptySet, FiniteSet, ParamDefWithParamType, ParamDefWithParamSet};
mod fact;
use fact::{Fact, InFact, NotInFact, IsCartFact, NotIsCartFact, IsTupleFact, NotIsTupleFact, AtomicFact, NormalAtomicFact, NotNormalAtomicFact, EqualFact, NotEqualFact, SubsetFact, NotSubsetFact, SupersetFact, NotSupersetFact,
    LessFact, NotLessFact, GreaterFact, NotGreaterFact,
    LessEqualFact, NotLessEqualFact, GreaterEqualFact, NotGreaterEqualFact,
    IsSetFact, NotIsSetFact, IsNonemptySetFact, NotIsNonemptySetFact,
    IsFiniteSetFact, NotIsFiniteSetFact,
    ExistFact, FactInOrAtomicFact, FactInsideExistFact, NotExistFact, OrAtomicFact, TrueExistFact,
    OrFact, ForallFact, SpecFact, ForallFactWithIff, AndFact, ChainFact, AndSpecFacts,
    AndFactOrSpecFact, OrFactOrAndFactOrSpecFact,
};
mod result;
use result::{StmtResult, NonFactualStmtSuccess, FactVerifiedByFact, FactVerifiedByBuiltinRules, StmtUnknown};
mod module_manager;
use module_manager::ModuleManager;
mod runtime_context;
use runtime_context::RuntimeContext;
mod environment;
use environment::Environment;
mod parse;
use parse::{Parser, TokenBlock, tokenize_line};
mod pipeline;

fn main() {
    try_atom_fn_obj();
    try_arithmetic();
    try_set_operations();
    try_stmt();
    try_equal_literally();
    try_list_set();
    try_set_builder();
    try_fn_set_without_params();
    try_fn_set_with_params();
    try_n_pos_obj();
    try_parameter_set();
    try_instantiated_struct_obj();
    try_cart_set_dim_proj_dim_tuple();
    try_count_range_closed_range_val();
    try_power_set_choice();
    try_atomic_fact();
    try_exist_fact();
    try_spec_fact();
    try_or_fact();
    try_forall_fact();
    try_forall_fact_with_iff();
    try_fact();
    try_errors();
    try_and_fact();
    try_and_fact_or_spec_fact();
    try_or_fact_or_and_fact_or_specific_fact();
    try_subset_superset_fact();
    try_stmt_result();
    try_definitions();
    try_obj_at_index();
    try_claim_stmt();
    try_know_stmt();
    try_proof_techniques();
    try_import_stmt();
    try_prove_stmt();
    try_run_file_stmt();
    try_prove_by_enumeration_stmt();
    try_have_obj_in_nonempty_set_stmt();
    try_tooling_stmt();
    try_prove_by_induction_stmt();
    try_have_obj_equal_stmt();
    try_eval_stmt();
    try_prove_for_stmt();
    try_have_obj_st_stmt();
    try_witness_stmt();
    try_prove_equal_set_stmt();
    try_witness_nonempty_set_stmt();
    try_view_fn_as_set();
    try_have_fn_equal_stmt();
    try_have_fn_equal_case_by_case_stmt();
    try_def_struct_stmt();
    try_module_manager();
    try_define_algorithm_stmt();
    try_runtime_context();
    try_tokenizer();
    try_tb();
    try_parser();
    try_parse_obj();
    try_parse_fact();
    try_parse_statements();
    try_executor();
    try_pipeline();
    try_calculate();
    try_obj_well_defined();
    try_verify_state();
}

fn try_atom_fn_obj() {
    let a_add_b = Obj::FnObj(FnObj::new(
        Obj::Identifier(Identifier::new("+")),
        vec![
            Obj::Identifier(Identifier::new("a")),
            Obj::Identifier(Identifier::new("b")),
        ],
    ));
    println!("{}", a_add_b);

    let a_add_b_with_mod = Obj::FnObj(FnObj::new(
        Obj::IdentifierWithMod(IdentifierWithMod::new("ModA", "name_a")),
        vec![
            Obj::Identifier(Identifier::new("a")),
            Obj::Identifier(Identifier::new("b")),
        ],
    ));
    println!("{}", a_add_b_with_mod);
}

fn try_arithmetic() {
    let number_one = Obj::Number(Number::new("1"));
    let number_two = Obj::Number(Number::new("2"));
    let one_add_two_result = Obj::Add(Add::new(number_one, number_two, true));
    let one_sub_two_result = Obj::Sub(Sub::new(Obj::Number(Number::new("1")), Obj::Number(Number::new("2")), true));
    let one_mul_two_result = Obj::Mul(Mul::new(Obj::Number(Number::new("1")), Obj::Number(Number::new("2")), true));
    let one_div_two_result = Obj::Div(Div::new(Obj::Number(Number::new("1")), Obj::Number(Number::new("2"))));
    let one_mod_two_result = Obj::Mod(Mod::new(Obj::Number(Number::new("1")), Obj::Number(Number::new("2")), true));
    let one_pow_two_result = Obj::Pow(Pow::new(Obj::Number(Number::new("1")), Obj::Number(Number::new("2")), true));
    println!("{}, {}, {}, {}, {}, {}",  one_add_two_result, one_sub_two_result, one_mul_two_result, one_div_two_result, one_mod_two_result, one_pow_two_result);
}

fn try_set_operations() {
    let mk = |s: &str| Obj::Identifier(Identifier::new(s));
    let union_result = Obj::Union(Union::new(mk("A"), mk("B")));
    let intersect_result = Obj::Intersect(Intersect::new(mk("A"), mk("B")));
    let set_minus_result = Obj::SetMinus(SetMinus::new(mk("A"), mk("B")));
    let disjoint_union_result = Obj::SetDiff(SetDiff::new(mk("A"), mk("B")));
    let cup_result = Obj::Cup(Cup::new(mk("A")));
    let cap_result = Obj::Cap(Cap::new(mk("A")));
    println!("{}, {}, {}, {}, {}, {}", union_result, intersect_result, set_minus_result, disjoint_union_result, cup_result, cap_result);
}

fn try_stmt() {
    let body3 = vec![
        Obj::Identifier(Identifier::new("a")),
        Obj::Identifier(Identifier::new("b")),
    ];
    let fact1 = Stmt::Fact(Fact::AtomicFact(AtomicFact::NormalAtomicFact(NormalAtomicFact::new(
        IdentifierOrIdentifierWithMod::Identifier(Identifier::new("p")),
        body3,
        Some((1, 0)),
    ))));
    println!("{}", fact1.to_string());

    let body2 = vec![
        Obj::Identifier(Identifier::new("a")),
        Obj::Identifier(Identifier::new("b")),
    ];
    let fact2 = Stmt::Fact(Fact::AtomicFact(AtomicFact::NormalAtomicFact(NormalAtomicFact::new(
        IdentifierOrIdentifierWithMod::IdentifierWithMod(IdentifierWithMod::new("ModA", "name_a")),
        body2,
        Some((1, 0)),
    ))));
    println!("{}", fact2);

    let def_let_param = vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))];
    let def_stmt = Stmt::DefStmt(DefStmt::DefLetStmt(DefLetStmt::new(def_let_param, vec![Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    )))], Some((1, 0)))));
    println!("{}", def_stmt);

    let def_stmt2 = Stmt::DefStmt(DefStmt::DefPropStmt(DefPropStmt::new("f".to_string(), vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))], Some(vec![Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    )))]), Some((1, 0)))));
    println!("{}", def_stmt2);
}

fn try_equal_literally() {
    let module_manager = ModuleManager::new();
    let syntactic_verifier = SyntacticVerifier::new(&module_manager);
    
    let a = Obj::Identifier(Identifier::new("a"));
    let b = Obj::Identifier(Identifier::new("b"));
    println!("{}", syntactic_verifier.equal_literally(&a, &b));
    let a2 = Obj::Identifier(Identifier::new("a"));
    println!("{}", syntactic_verifier.equal_literally(&a2, &a));
}

fn try_list_set() {
    let list_set = Obj::ListSet(ListSet::new(vec![
        Obj::Identifier(Identifier::new("a")),
        Obj::Identifier(Identifier::new("b")),
    ]));
    println!("{}", list_set);
}

fn try_set_builder() {
    let set_builder = Obj::SetBuilder(SetBuilder::new("a".to_string(), Obj::Identifier(Identifier::new("b")), vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))))))]));
    println!("{}", set_builder);
}

fn try_fn_set_without_params() {
    let fn_set_without_params = Obj::FnSetWithoutDom(FnSetWithoutDom::new(
        vec![
            Obj::Identifier(Identifier::new("a")),
            Obj::Identifier(Identifier::new("b")),
        ],
        Obj::Identifier(Identifier::new("c")),
    ));
    println!("{}", fn_set_without_params);
}

fn try_fn_set_with_params() {
    let fn_set_with_params = Obj::FnSetWithDom(FnSetWithDom::new(vec![ParamDefWithParamSet(vec!["a".to_string()], Obj::Identifier(Identifier::new("a"))), ParamDefWithParamSet(vec!["b".to_string()], Obj::Identifier(Identifier::new("b")))], vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))))))], Obj::Identifier(Identifier::new("c"))));
    println!("{}", fn_set_with_params);

    let fn_set_with_params2 = Obj::FnSetWithDom(FnSetWithDom::new(vec![ParamDefWithParamSet(vec!["a".to_string()], Obj::Identifier(Identifier::new("a"))), ParamDefWithParamSet(vec!["b".to_string()], Obj::Identifier(Identifier::new("b"))), ParamDefWithParamSet(vec!["c".to_string()], Obj::Identifier(Identifier::new("c")))], vec![], Obj::Identifier(Identifier::new("c"))));
    println!("{}", fn_set_with_params2);
}

fn try_n_pos_obj() {
    let n_pos_obj = Obj::NPosObj(NPosObj::new());
    println!("{}", n_pos_obj);
    let n_obj = Obj::NObj(NObj::new());
    println!("{}", n_obj);
    let q_obj = Obj::QObj(QObj::new());
    println!("{}", q_obj);
    let z_obj = Obj::ZObj(ZObj::new());
    println!("{}", z_obj);
    let r_obj = Obj::RObj(RObj::new());
    println!("{}", r_obj);
    let q_pos_obj = Obj::QPos(QPos::new());
    println!("{}", q_pos_obj);
    let z_pos_obj = Obj::ZPos(ZPos::new());
    println!("{}", z_pos_obj);
    let r_pos_obj = Obj::RPos(RPos::new());
    println!("{}", r_pos_obj);
    let q_neg_obj = Obj::QNeg(QNeg::new());
    println!("{}", q_neg_obj);
    let z_neg_obj = Obj::ZNeg(ZNeg::new());
    println!("{}", z_neg_obj);
    let r_neg_obj = Obj::RNeg(RNeg::new());
    println!("{}", r_neg_obj);
    let q_n0_obj = Obj::QNz(QNz::new());
    println!("{}", q_n0_obj);
    let z_n0_obj = Obj::ZNz(ZNz::new());
    println!("{}", z_n0_obj);
    let r_n0_obj = Obj::RNz(RNz::new());
    println!("{}", r_n0_obj);
}

fn try_parameter_set() {
    let parameter_set = ParamType::Set(Set::new());
    println!("{}", parameter_set);
    let nonempty_parameter_set = ParamType::NonemptySet(NonemptySet::new());
    println!("{}", nonempty_parameter_set);
    let finite_parameter_set = ParamType::FiniteSet(FiniteSet::new());
    println!("{}", finite_parameter_set);
    let obj_parameter_set = ParamType::Obj(Obj::Identifier(Identifier::new("a")));
    println!("{}", obj_parameter_set);
}

fn try_instantiated_struct_obj() {
    let instantiated_struct_obj = Obj::InstSetStructObj(InstStructObj::new(
        IdentifierOrIdentifierWithMod::Identifier(Identifier::new("A")),
        vec![Obj::Identifier(Identifier::new("b"))],
    ));
    println!("{}", instantiated_struct_obj);

    let instantiated_struct_obj2 = Obj::InstSetStructObj(InstStructObj::new(
        IdentifierOrIdentifierWithMod::Identifier(Identifier::new("a")),
        vec![],
    ));
    println!("{}", instantiated_struct_obj2);
}


fn try_cart_set_dim_proj_dim_tuple() {
    let mk = |s: &str| Obj::Identifier(Identifier::new(s));
    let cart = Obj::Cart(Cart::new(vec![mk("a"), mk("b")]));
    let set_dim = Obj::CartDim(CartDim::new(mk("a")));
    let proj = Obj::Proj(Proj::new(mk("a"), mk("b")));
    let dim = Obj::Dim(Dim::new(mk("b")));
    println!("{}", cart);
    println!("{}", set_dim);
    println!("{}", proj);
    println!("{}", dim);
    let tuple = Obj::Tuple(Tuple::new(vec![mk("a"), mk("b")]));
    println!("{}", tuple);
}

fn try_count_range_closed_range_val() {
    let mk = |s: &str| Obj::Identifier(Identifier::new(s));
    let count = Obj::Count(Count::new(mk("a")));
    let range = Obj::Range(Range::new(mk("a"), mk("b")));
    let closed_range = Obj::ClosedRange(ClosedRange::new(mk("a"), mk("b")));
    let val = Obj::Val(Val::new(mk("a")));
    println!("{}", count);
    println!("{}", range);
    println!("{}", closed_range);
    println!("{}", val);
}

fn try_power_set_choice() {
    let mk = |s: &str| Obj::Identifier(Identifier::new(s));
    let power_set = Obj::PowerSet(PowerSet::new(mk("a")));
    let choice = Obj::Choose(Choose::new(mk("b")));
    println!("{}", power_set);
    println!("{}", choice);
}

fn try_atomic_fact() {
    let line = 1usize;
    let _normal = AtomicFact::NormalAtomicFact(NormalAtomicFact::new(
        IdentifierOrIdentifierWithMod::Identifier(Identifier::new("p")),
        vec![Obj::mk("a"), Obj::mk("b")],
        Some((line, 0)),
    ));
    let _equal = AtomicFact::EqualFact(EqualFact::new(Obj::mk("x"), Obj::mk("y"), Some((line, 0))));
    let _less = AtomicFact::LessFact(LessFact::new(Obj::mk("a"), Obj::mk("b"), Some((line, 0))));
    let _greater = AtomicFact::GreaterFact(GreaterFact::new(Obj::mk("a"), Obj::mk("b"), Some((line, 0))));
    let _less_equal = AtomicFact::LessEqualFact(LessEqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((line, 0))));
    let _greater_equal = AtomicFact::GreaterEqualFact(GreaterEqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((line, 0))));
    let _is_set = AtomicFact::IsSetFact(IsSetFact::new(Obj::mk("S"), Some((line, 0))));
    let _is_nonempty_set = AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(Obj::mk("S"), Some((line, 0))));
    let _is_finite_set = AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(Obj::mk("S"), Some((line, 0))));
    let _is_cart = AtomicFact::IsCartFact(IsCartFact::new(Obj::mk("S"), Some((line, 0))));
    let _not_is_cart = AtomicFact::NotIsCartFact(NotIsCartFact::new(Obj::mk("S"), Some((line, 0))));

    let _not_normal = AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact::new(
        IdentifierOrIdentifierWithMod::Identifier(Identifier::new("p")),
        vec![Obj::mk("a")],
        Some((line, 0)),
    ));
    let _not_equal = AtomicFact::NotEqualFact(NotEqualFact::new(Obj::mk("x"), Obj::mk("y"), Some((line, 0))));
    let _not_less = AtomicFact::NotLessFact(NotLessFact::new(Obj::mk("a"), Obj::mk("b"), Some((line, 0))));
    let _not_greater = AtomicFact::NotGreaterFact(NotGreaterFact::new(Obj::mk("a"), Obj::mk("b"), Some((line, 0))));
    let _not_less_equal = AtomicFact::NotLessEqualFact(NotLessEqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((line, 0))));
    let _not_greater_equal = AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((line, 0))));
    let _not_is_set = AtomicFact::NotIsSetFact(NotIsSetFact::new(Obj::mk("S"), Some((line, 0))));
    let _not_is_nonempty_set = AtomicFact::NotIsNonemptySetFact(NotIsNonemptySetFact::new(Obj::mk("S"), Some((line, 0))));
    let _not_is_finite_set = AtomicFact::NotIsFiniteSetFact(NotIsFiniteSetFact::new(Obj::mk("S"), Some((line, 0))));
    println!("{}", _normal);
    println!("{}", _equal);
    println!("{}", _less);
    println!("{}", _greater);
    println!("{}", _less_equal);
    println!("{}", _greater_equal);
    println!("{}", _is_set);
    println!("{}", _is_nonempty_set);
    println!("{}", _is_finite_set);
    println!("{}", _not_normal);
    println!("{}", _not_equal);
    println!("{}", _not_less);
    println!("{}", _not_greater);
    println!("{}", _not_less_equal);
    println!("{}", _not_greater_equal);
    println!("{}", _not_is_set);
    println!("{}", _not_is_nonempty_set);
    println!("{}", _not_is_finite_set);
    println!("{}", _is_cart);
    println!("{}", _not_is_cart);

    let _in = AtomicFact::InFact(InFact::new(Obj::mk("a"), Obj::mk("S"), Some((line, 0))));
    let _not_in = AtomicFact::NotInFact(NotInFact::new(Obj::mk("a"), Obj::mk("S"), Some((line, 0))));
    println!("{}", _in);
    println!("{}", _not_in);

    let _is_tuple = AtomicFact::IsTupleFact(IsTupleFact::new(Obj::mk("t"), Some((line, 0))));
    let _not_is_tuple = AtomicFact::NotIsTupleFact(NotIsTupleFact::new(Obj::mk("t"), Some((line, 0))));
    println!("{}", _is_tuple);
    println!("{}", _not_is_tuple);
}

fn try_exist_fact() {
    let _true_exist = ExistFact::TrueExistFact(TrueExistFact::new(
        vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))],
        vec![FactInsideExistFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0)))))],
        Some((1, 0)),
    ));
    let _not_exist = ExistFact::NotExistFact(NotExistFact::new(
        vec![ParamDefWithParamType(vec!["y".to_string()], ParamType::Set(Set::new()))],
        vec![FactInsideExistFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0)))))],
        Some((2, 0)),
    ));
    println!("{}", _true_exist);
    println!("{}", _not_exist);

    let _true_exist2 = ExistFact::TrueExistFact(TrueExistFact::new(
        vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))],
        vec![FactInsideExistFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))))), FactInsideExistFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("c"), Obj::mk("d"), Some((1, 0)))))],
        Some((1, 0)),
    ));
    println!("{}", _true_exist2);

    let _true_exist3 = ExistFact::TrueExistFact(TrueExistFact::new(
        vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))],
        vec![FactInsideExistFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))))), FactInsideExistFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("c"), Obj::mk("d"), Some((1, 0)))))],
        Some((1, 0)),
    ));
    println!("{}", _true_exist3);
}

fn try_spec_fact() {
    let _spec_atom = SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0)))));
    let ef = ExistFact::TrueExistFact(TrueExistFact::new(
        vec![ParamDefWithParamType(vec!["u".to_string()], ParamType::Set(Set::new()))],
        vec![FactInsideExistFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("u"), Obj::mk("v"), Some((1, 0)))))],
        Some((1, 0)),
    ));
    let _spec_exist = SpecFact::ExistFact(ef);
    println!("{}", _spec_atom);
    println!("{}", _spec_exist);
}

fn try_or_fact() {
    let o = OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))));
    let _ = o.key();
    let facts = vec![
        AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            Obj::mk("p"),
            Obj::mk("q"),
            Some((1, 0)),
        )))),
    ];
    let _or = OrFact::new(facts, Some((1, 0)));
    println!("{}", _or);

    let facts2 = vec![
        AndFactOrSpecFact::AndFact(AndFact::ChainFact(ChainFact::new(vec![Obj::mk("p"), Obj::mk("q"), Obj::mk("r")], vec![IdentifierOrIdentifierWithMod::Identifier(Identifier::new("p")), IdentifierOrIdentifierWithMod::Identifier(Identifier::new("q"))], Some((1, 0))))),
    ];
    let _or2 = OrFact::new(facts2, Some((1, 0)));
    println!("{}", _or2);
}

fn try_and_fact_or_spec_fact() {
    let _spec = AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("a"),
        Obj::mk("b"),
        Some((1, 0)),
    ))));
    println!("{}", _spec);

    let facts = vec![
        SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            Obj::mk("p"),
            Obj::mk("q"),
            Some((1, 0)),
        ))),
        SpecFact::AtomicFact(AtomicFact::LessFact(LessFact::new(
            Obj::mk("x"),
            Obj::mk("y"),
            Some((2, 0)),
        ))),
    ];
    let _and = AndFactOrSpecFact::AndFact(AndFact::AndSpecFacts(AndSpecFacts::new(facts, Some((1, 0)))));
    println!("{}", _and);
}

fn try_forall_fact() {
    let param_type_or_property_pairs = vec![ParamDefWithParamType(vec!["n".to_string()], ParamType::Set(Set::new()))];
    let dom_facts = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
        EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
    )))];
    let then_facts = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
        EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
    )))];
    let _forall = ForallFact::new(param_type_or_property_pairs, dom_facts, then_facts, Some((1, 0)));
    println!("{}", _forall);

    let param_type_or_property_pairs2 = vec![ParamDefWithParamType(vec!["n".to_string(), "m".to_string()], ParamType::Set(Set::new()))];
    let dom_facts2 = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
        EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
    )))];
    let then_facts2 = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
        EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
    )))];
    let _forall2 = ForallFact::new(param_type_or_property_pairs2, dom_facts2, then_facts2, Some((1, 0)));
    println!("{}", _forall2);

    let param_type_or_property_pairs3 = vec![ParamDefWithParamType(vec!["n".to_string(), "m".to_string()], ParamType::Set(Set::new()))];
    let dom_facts3 = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
        EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
    )))];
    let then_facts3 = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
        EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
    )))];
    let _forall3 = ForallFact::new(param_type_or_property_pairs3, dom_facts3, then_facts3, Some((1, 0)));
    println!("{}", _forall3);
}

fn try_forall_fact_with_iff() {
    let param_type_or_property_pairs = vec![ParamDefWithParamType(vec!["n".to_string()], ParamType::Set(Set::new()))];
    let dom_facts = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
        EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
    )))];
    let then_facts = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
        EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
    )))];
    let forall = ForallFact::new(param_type_or_property_pairs, dom_facts, then_facts, Some((1, 0)));

    let _forall_fact_with_iff = ForallFactWithIff::new(forall, vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
        EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
    )))], Some((2, 0)));
    println!("{}", _forall_fact_with_iff);
}


fn try_fact() {
    let af = AtomicFact::EqualFact(EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))));
    let _f_atom = Fact::AtomicFact(af);
    let ef = ExistFact::TrueExistFact(TrueExistFact::new(
        vec![ParamDefWithParamType(vec!["u".to_string()], ParamType::Set(Set::new()))],
        vec![FactInsideExistFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("u"), Obj::mk("v"), Some((1, 0)))))],
        Some((1, 0)),
    ));
    let _f_exist = Fact::ExistFact(ef);
    let _f_or = Fact::OrFact(OrFact::new(vec![], Some((1, 0))));
    let _f_forall = Fact::ForallFact(ForallFact::new(
        vec![ParamDefWithParamType(vec!["n".to_string()], ParamType::Set(Set::new()))],
        vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
            EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
        )))],
        vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
            EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
        )))],
        Some((1, 0)),
    ));
    let _f_forall_fact_with_iff = Fact::ForallFactWithIff(ForallFactWithIff::new(ForallFact::new(
        vec![ParamDefWithParamType(vec!["n".to_string()], ParamType::Set(Set::new()))],
        vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
            EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
        )))],
        vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
            EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
        )))], Some((1, 0))), vec![], Some((1, 0))));

    let facts = vec![
        SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            Obj::mk("p"),
            Obj::mk("q"),
            Some((1, 0)),
        ))),
    ];
    let _f_and = Fact::AndFact(AndFact::AndSpecFacts(AndSpecFacts::new(facts, Some((1, 0)))));
    println!("{}", _f_and);
}

fn try_errors() {
    let _err = ArithmeticError::new("demo");

    println!("{}", _err);

    let err: StmtError = StmtError::ArithmeticError(ArithmeticError::new("demo"));
    println!("{}", err);

    let err: StmtError = StmtError::NewAtomicFactError(NewAtomicFactError::new("demo"));
    println!("{}", err);

    let err: StmtError = StmtError::StoreFactError(StoreFactError::new("demo"));
    println!("{}", err);

    let err: StmtError = StmtError::ParseBlockError(ParseBlockError::ExpectedIndent(1, 0));
    println!("{}", err);

    let err: StmtError = StmtError::ParsingError(ParsingError::new("demo", (1, 0)));
    println!("{}", err);

    let err: StmtError = StmtError::ExecError(ExecError::new("demo", vec![], Some((1, 0))));
    println!("{}", err);

    let err: StmtError = StmtError::WellDefinedError(WellDefinedError::new("demo", vec![StmtError::ArithmeticError(ArithmeticError::new("demo"))], Some((1, 0))));
    println!("{}", err);
}

fn try_and_fact() {
    let facts = vec![
        SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            Obj::mk("p"),
            Obj::mk("q"),
            Some((1, 0)),
        ))),
    ];
    let _and = AndFact::AndSpecFacts(AndSpecFacts::new(facts, Some((1, 0))));
    println!("{}", _and);
}

fn try_or_fact_or_and_fact_or_specific_fact() {
    let fact1: OrFactOrAndFactOrSpecFact = OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))));
    println!("{}", fact1);

    let fact2: OrFactOrAndFactOrSpecFact = OrFactOrAndFactOrSpecFact::AndFact(AndFact::AndSpecFacts(AndSpecFacts::new(vec![SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    )))], Some((1, 0)))));
    println!("{}", fact2);

    let fact3: OrFactOrAndFactOrSpecFact = OrFactOrAndFactOrSpecFact::OrFact(OrFact::new(vec![AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))], Some((1, 0))));
    println!("{}", fact3);
}

fn try_subset_superset_fact() {
    let subset = AtomicFact::SubsetFact(SubsetFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))));
    let superset = AtomicFact::SupersetFact(SupersetFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))));
    let not_subset = AtomicFact::NotSubsetFact(NotSubsetFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))));
    let not_superset = AtomicFact::NotSupersetFact(NotSupersetFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))));
    println!("{}", subset);
    println!("{}", superset);
    println!("{}", not_subset);
    println!("{}", not_superset);

    let subset_fact = Fact::AtomicFact(subset);
    let superset_fact = Fact::AtomicFact(superset);
    let not_subset_fact = Fact::AtomicFact(not_subset);
    let not_superset_fact = Fact::AtomicFact(not_superset);
    println!("{}", subset_fact);
    println!("{}", superset_fact);
    println!("{}", not_subset_fact);
    println!("{}", not_superset_fact);
}

fn try_stmt_result() {
    let stmt = Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))));
    let result = StmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(stmt.to_string(), None));
    println!("{}", result);


    let fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    )));
    let unknown = StmtUnknown::new();
    let result = StmtResult::StmtUnknown(unknown);
    println!("{}", result);

    let fact_verified_by_fact = FactVerifiedByFact::new(fact.to_string(), fact.to_string(), None);
    let result = StmtResult::FactVerifiedByFact(fact_verified_by_fact);
    println!("{}", result);

    let fact_verified_by_builtin_rules = FactVerifiedByBuiltinRules::new(fact.to_string(), "demo".to_string(), None);
    let result = StmtResult::FactVerifiedByBuiltinRules(fact_verified_by_builtin_rules);
    println!("{}", result);
}

fn try_definitions() {
    let params_def_with_type = vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))];
    let def_prop_stmt = DefPropStmt::new("f".to_string(), params_def_with_type, Some(vec![Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    )))]), Some((1, 0)));
    println!("{}", def_prop_stmt);

    let def_let_param = vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))];
    let def_let_stmt = DefLetStmt::new(def_let_param, vec![Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    )))], Some((1, 0)));
    println!("{}", def_let_stmt);

    let params_def_with_type2 = vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))];
    let def_prop_stmt2 = DefPropStmt::new("f".to_string(), params_def_with_type2, None, Some((1, 0)));
    println!("{}", def_prop_stmt2);
}

fn try_obj_at_index() {
    let obj = Obj::ObjAtIndex(ObjAtIndex::new(Obj::mk("a"), Obj::mk("b")));
    println!("{}", obj);
}

fn try_claim_stmt() {
    let proof = vec![Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))];
    let claim_stmt = ClaimStmt::new(
        Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            Obj::mk("p"),
            Obj::mk("q"),
            Some((1, 0)),
        ))),
        proof,
        Some((1, 0)),
    );
    println!("{}", claim_stmt);

    let stmt = Stmt::ClaimStmt(claim_stmt);
    println!("{}", stmt);
}

fn try_know_stmt() {
    let know_stmt = KnowStmt::new(vec![Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    )))], Some((1, 0)));
    println!("{}", know_stmt);

    let stmt = Stmt::KnowStmt(know_stmt);
    println!("{}", stmt);
}

fn try_proof_techniques() {

    let impossible_fact = OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))));
    let prove_case_by_case = ProveCaseByCaseStmt::new(vec![AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))], vec![Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    )))], vec![vec![Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0))))))]], vec![Some(impossible_fact)], Some((1, 0)));
    println!("{}", prove_case_by_case);

    let impossible_fact = OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))));

    let claim_prove_by_contradiction_stmt = ProveByContradictionStmt::new(Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))), vec![Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))], impossible_fact, Some((1, 0)));
    println!("{}", claim_prove_by_contradiction_stmt);

    let proof_technique = ProofTechniqueStmt::ProveCaseByCase(prove_case_by_case);
    println!("{}", proof_technique);

    let proof_technique = ProofTechniqueStmt::ProveByContradiction(claim_prove_by_contradiction_stmt);
    println!("{}", proof_technique);

    let stmt = Stmt::ProofTechnique(proof_technique);
    println!("{}", stmt);
}

fn try_import_stmt() {
    let import_relative_path_stmt = ImportRelativePathStmt::new("path/to/mod", Some("mod".to_string()), Some((1, 0)));
    println!("{}", import_relative_path_stmt);

    let import_global_mod_stmt = ImportGlobalModuleStmt::new("mod", Some("mod".to_string()), Some((1, 0)));
    println!("{}", import_global_mod_stmt);

    let stmt = Stmt::ToolingStmt(ToolingStmt::Import(ImportStmt::ImportRelativePath(import_relative_path_stmt)));
    println!("{}", stmt);

    let stmt = Stmt::ToolingStmt(ToolingStmt::Import(ImportStmt::ImportGlobalModule(import_global_mod_stmt)));
    println!("{}", stmt);
}

fn try_prove_stmt() {
    let proof = vec![Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))];
    let prove_stmt = ProveStmt::new(proof, Some((1, 0)));
    println!("{}", prove_stmt);

    let stmt = Stmt::ProveStmt(prove_stmt);
    println!("{}", stmt);
}

fn try_run_file_stmt() {
    let run_file_stmt = RunFileStmt::new("path/to/file.txt", Some((1, 0)));
    println!("{}", run_file_stmt);

    let stmt = Stmt::ToolingStmt(ToolingStmt::RunFile(run_file_stmt));
    println!("{}", stmt);
}

fn try_prove_by_enumeration_stmt() {
    let params = vec!["x".to_string()];
    let param_sets = vec![Obj::mk("p")];
    let proof = vec![Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))];

    let to_prove = vec![Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    )))];
    
    let prove_by_enumeration_stmt = ProveByEnumerationStmt::new(params, param_sets, to_prove, proof, Some((1, 0)));
    println!("{}", prove_by_enumeration_stmt);

    let stmt = Stmt::ProofTechnique(ProofTechniqueStmt::ProveByEnumeration(prove_by_enumeration_stmt));
    println!("{}", stmt);
}

fn try_have_obj_in_nonempty_set_stmt() {
    let have_obj_in_nonempty_set_stmt = HaveObjInNonemptySetOrParamTypeStmt::new(vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))], Some((1, 0)));
    println!("{}", have_obj_in_nonempty_set_stmt);

    let stmt = Stmt::DefStmt(DefStmt::HaveObjInNonemptySetStmt(have_obj_in_nonempty_set_stmt));
    println!("{}", stmt);
}

fn try_tooling_stmt() {
    let import_relative_path_stmt = ImportRelativePathStmt::new("path/to/mod", Some("mod".to_string()), Some((1, 0)));
    println!("{}", import_relative_path_stmt);

    let import_global_mod_stmt = ImportGlobalModuleStmt::new("mod", Some("mod".to_string()), Some((1, 0)));
    println!("{}", import_global_mod_stmt);

    let stmt = Stmt::ToolingStmt(ToolingStmt::Import(ImportStmt::ImportRelativePath(import_relative_path_stmt)));
    println!("{}", stmt);

    let stmt = Stmt::ToolingStmt(ToolingStmt::Import(ImportStmt::ImportGlobalModule(import_global_mod_stmt)));
    println!("{}", stmt);

    let clear_stmt = ClearStmt::new(Some((1, 0)));
    println!("{}", clear_stmt);

    let stmt = Stmt::ToolingStmt(ToolingStmt::Clear(clear_stmt));
    println!("{}", stmt);

    let do_nothing_stmt = DoNothingStmt::new(Some((1, 0)));
    println!("{}", do_nothing_stmt);

    let stmt = Stmt::ToolingStmt(ToolingStmt::DoNothing(do_nothing_stmt));
    println!("{}", stmt);
}

fn try_prove_by_induction_stmt() {
    let fact = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))];
    let param = "x".to_string();
    let proof = vec![Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))];
    let induc_from = Obj::mk("N");
    let prove_by_induction_stmt = ProveByInductionStmt::new(fact, param, proof, induc_from, Some((1, 0)));
    println!("{}", prove_by_induction_stmt);

    let stmt = Stmt::ProofTechnique(ProofTechniqueStmt::ProveByInduction(prove_by_induction_stmt));
    println!("{}", stmt);
}

fn try_have_obj_equal_stmt() {
    let have_obj_equal_param = vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))];
    let have_obj_equal_stmt = HaveObjEqualStmt::new(have_obj_equal_param, vec![Obj::mk("p")], Some((1, 0)));
    println!("{}", have_obj_equal_stmt);

    let stmt = Stmt::DefStmt(DefStmt::HaveObjEqualStmt(have_obj_equal_stmt));
    println!("{}", stmt);
}


fn try_eval_stmt() {
    let eval_stmt = EvalStmt::new(Obj::mk("p"), Some((1, 0)));
    println!("{}", eval_stmt);

    let stmt = Stmt::EvalStmt(eval_stmt);
    println!("{}", stmt);

    let stmt = Stmt::EvalStmt(EvalStmt::new(Obj::mk("p"), Some((1, 0))));
    println!("{}", stmt);
}

fn try_prove_for_stmt() {
    let params = vec!["x".to_string()];
    let param_sets = ClosedRangeOrRange::ClosedRange(ClosedRange::new(Obj::mk("0"), Obj::mk("10")));
    let dom_facts = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))];
    let then_facts = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))];
    let proof = vec![Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))];
    let prove_for_stmt = ProveForStmt::new(params, vec![param_sets], dom_facts, then_facts, proof, Some((1, 0)));
    println!("{}", prove_for_stmt);

    let stmt = Stmt::ProofTechnique(ProofTechniqueStmt::ProveForStmt(prove_for_stmt));
    println!("{}", stmt);

    let params2 = vec!["x".to_string()];
    
    let param_sets2 = ClosedRangeOrRange::Range(Range::new(Obj::mk("0"), Obj::mk("10")));
    let dom_facts2 = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))];
    let then_facts2 = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))];

    let proof2 = vec![Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))];
    
    let prove_for_stmt = ProveForStmt::new(params2, vec![param_sets2], dom_facts2, then_facts2, proof2, Some((1, 0)));
    println!("{}", prove_for_stmt);

    let stmt = Stmt::ProofTechnique(ProofTechniqueStmt::ProveForStmt(prove_for_stmt));
    println!("{}", stmt);
}

fn try_have_obj_st_stmt() {
    let have_obj_st_stmt = HaveExistObjStmt::new(TrueExistFact::new(vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))], vec![], Some((1, 0))), Some((1, 0)));
    println!("{}", have_obj_st_stmt);

    let stmt = Stmt::DefStmt(DefStmt::HaveExistObjStmt(have_obj_st_stmt));
    println!("{}", stmt);
}

fn try_witness_stmt() {
    let witness_exist_fact = WitnessExistFact::new(vec![Obj::mk("p")], TrueExistFact::new(vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))], vec![FactInsideExistFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0)))))], Some((1, 0))), vec![], Some((1, 0)));
    println!("{}", witness_exist_fact);

    let stmt = Stmt::WitnessStmt(WitnessStmt::WitnessExistFact(witness_exist_fact));
    println!("{}", stmt);
}

fn try_prove_equal_set_stmt() {
    let prove_equal_set_stmt = ProveByEqualSetStmt::new(Obj::mk("p"), Obj::mk("q"), vec![], Some((1, 0)));
    println!("{}", prove_equal_set_stmt);

    let stmt = Stmt::ProofTechnique(ProofTechniqueStmt::ProveByEqualSet(prove_equal_set_stmt));
    println!("{}", stmt);

    let proof2 = vec![Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("p"),
        Obj::mk("q"),
        Some((1, 0)),
    ))))];

    let prove_equal_set_stmt = ProveByEqualSetStmt::new(Obj::mk("p"), Obj::mk("q"), proof2, Some((1, 0)));
    println!("{}", prove_equal_set_stmt);

    let stmt = Stmt::ProofTechnique(ProofTechniqueStmt::ProveByEqualSet(prove_equal_set_stmt));
    println!("{}", stmt);
}

fn try_witness_nonempty_set_stmt() {
    let witness_nonempty_set_stmt = WitnessNonemptySet::new(Obj::mk("p"), Obj::mk("q"), vec![], Some((1, 0)));
    println!("{}", witness_nonempty_set_stmt);

    let stmt = Stmt::WitnessStmt(WitnessStmt::WitnessNonemptySet(witness_nonempty_set_stmt));
    println!("{}", stmt);
}

fn try_view_fn_as_set() {
    let prove_fn_set_is_subset_of_cart_set_stmt = ViewFnAsSetStmt::new(Obj::mk("p"), Some((1, 0)));
    println!("{}", prove_fn_set_is_subset_of_cart_set_stmt);

    let stmt = Stmt::ProofTechnique(ProofTechniqueStmt::ViewFnAsSet(prove_fn_set_is_subset_of_cart_set_stmt));
    println!("{}", stmt);

    let prove_fn_set_is_subset_of_cart_set_stmt = ViewFnAsSetStmt::new(Obj::mk("p"), Some((1, 0)));
    println!("{}", prove_fn_set_is_subset_of_cart_set_stmt);

    let stmt = Stmt::ProofTechnique(ProofTechniqueStmt::ViewFnAsSet(prove_fn_set_is_subset_of_cart_set_stmt));
    println!("{}", stmt);
}

fn try_have_fn_equal_stmt() {
    let have_fn_equal_stmt = 
    HaveFnEqualStmt::new("f".to_string(), FnSetWithDom::new(vec![ParamDefWithParamSet(vec!["x".to_string()], Obj::mk("p"))], vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))))))], Obj::mk("p")), Obj::mk("p"), Some((1, 0)));
    have_fn_equal_stmt.to_string();
    println!("{}", have_fn_equal_stmt);

    let stmt = Stmt::DefStmt(DefStmt::HaveFnEqualStmt(have_fn_equal_stmt));
    println!("{}", stmt);
}

fn try_have_fn_equal_case_by_case_stmt() {
    let have_fn_equal_case_by_case_stmt = HaveFnEqualCaseByCaseStmt::new("f".to_string(), FnSetWithDom::new(vec![ParamDefWithParamSet(vec!["x".to_string()], Obj::mk("p"))], vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))))))], Obj::mk("p")), vec![AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))))))], vec![Obj::mk("p")], Some((1, 0)));
    println!("{}", have_fn_equal_case_by_case_stmt);

    let stmt = Stmt::DefStmt(DefStmt::HaveFnEqualCaseByCaseStmt(have_fn_equal_case_by_case_stmt));
    println!("{}", stmt);
}

fn try_def_struct_stmt() {
    let params_def_with_type = vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))];
    let def_struct_stmt = DefStructWithNoFieldStmt::new("A".to_string(), params_def_with_type, vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))))))], Obj::mk("p"), Some((1, 0)));
    println!("{}", def_struct_stmt);

    let stmt = Stmt::DefStmt(DefStmt::DefStructStmt(DefStructStmt::DefStructWithNoFieldStmt(def_struct_stmt)));
    println!("{}", stmt);

    let fields = vec![(String::from("x"), OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0)))))))];
    let def_struct_stmt = DefStructStmt::DefStructWithFieldsStmt(DefStructWithFieldsStmt::new("A".to_string(), vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))], fields, vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))))))], Some((1, 0))));
    println!("{}", def_struct_stmt);

    let stmt = Stmt::DefStmt(DefStmt::DefStructStmt(def_struct_stmt));
    println!("{}", stmt);
}

fn try_module_manager() {
    let module_manager = ModuleManager::new();
    println!("{}", module_manager);
}

fn try_define_algorithm_stmt() {
    let return_or_algo_if = vec![AlgoReturnOrAlgoIf::AlgoIf(AlgoIf::new(AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0)))))), AlgoReturn::new(Obj::mk("p"), Some((1, 0))), Some((1, 0)))), AlgoReturnOrAlgoIf::AlgoReturn(AlgoReturn::new(Obj::mk("p"), Some((1, 0))))];

    println!("{} on {:?}", return_or_algo_if[0], return_or_algo_if[0].line_file());
    println!("{} on {:?}", return_or_algo_if[1], return_or_algo_if[1].line_file());
    
    let define_algorithm_stmt = DefAlgoStmt::new("f".to_string(), vec!["x".to_string()], return_or_algo_if, Some((1, 0)));
    println!("{}", define_algorithm_stmt);

    let stmt = Stmt::DefStmt(DefStmt::DefAlgoStmt(define_algorithm_stmt));
    println!("{}", stmt);
}

fn try_runtime_context() {
    let mut module_manager = ModuleManager::new();

    let fn_set_obj = FnSetObj::FnSetWithoutDom(FnSetWithoutDom::new(vec![Obj::mk("p")], Obj::mk("p")));
    println!("{}", fn_set_obj);

    let fn_set_obj = FnSetObj::FnSetWithDom(FnSetWithDom::new(vec![ParamDefWithParamSet(vec!["x".to_string()], Obj::mk("p"))], vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))))))], Obj::mk("p")));
    println!("{}", fn_set_obj);

    let environment: Box<Environment> = Box::new(Environment::new(HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new()));

    let builtin_environment: Box<Environment> = Box::new(Environment::new(HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new()));
    
    let mut runtime_context = RuntimeContext::new(&mut module_manager, vec![environment], builtin_environment, HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new());
    println!("{}", runtime_context);

    let atomic_fact = AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))));
    println!("{}", atomic_fact.key());

    let stored_fact_result = runtime_context.top_level_env().store_fact(Fact::AtomicFact(atomic_fact));
    if stored_fact_result.is_err() {
        println!("ERROR:{}", stored_fact_result.err().unwrap());
    }

    println!("{}", runtime_context.top_level_env());

    let exist_fact = ExistFact::TrueExistFact(TrueExistFact::new(
        vec![ParamDefWithParamType(vec!["x".to_string()], ParamType::Set(Set::new()))],
        vec![
            FactInsideExistFact::OrAtomicFact(OrAtomicFact {
                facts: vec![
                    FactInOrAtomicFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))))),
                    FactInOrAtomicFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0))))),
                ],
                line_file_index: Some((1, 0)),
            }),
            FactInsideExistFact::OrAtomicFact(OrAtomicFact {
                facts: vec![FactInOrAtomicFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("p"), Obj::mk("q"), Some((1, 0)))))],
                line_file_index: Some((1, 0)),
            }),
        ],
        Some((1, 0)),
    ));
    for f in exist_fact.facts() {
        let _ = f.line_file_index();
    }
    println!("{}", exist_fact.key());
    let stored_fact_result = runtime_context.top_level_env().store_fact(Fact::ExistFact(exist_fact));
    if stored_fact_result.is_err() {
        println!("ERROR:{}", stored_fact_result.err().unwrap());
    }
    println!("{}", runtime_context.top_level_env());

    let param_type_or_property_pairs = vec![ParamDefWithParamType(vec!["n".to_string()], ParamType::Set(Set::new()))];
    let dom_facts = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
        EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
    )))];
    let then_facts = vec![OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(
        EqualFact::new(Obj::mk("a"), Obj::mk("b"), Some((1, 0))),
    )))];
    let _forall = ForallFact::new(param_type_or_property_pairs, dom_facts, then_facts, Some((1, 0)));
    
    let stored_fact_result = runtime_context.top_level_env().store_fact(Fact::ForallFact(_forall));
    if stored_fact_result.is_err() {
        println!("ERROR:{}", stored_fact_result.err().unwrap());
    }
    
}

fn try_tokenizer() {
    let line = "a+b";
    let tokens = tokenize_line(line);
    println!("{:?}", tokens);
}

fn try_tb() {
    let s = "a:\n    b\n  c";
    let blocks = TokenBlock::parse_blocks(s, 0);
    println!("{:?}", blocks);
}

fn try_parser() {
    let parser = Parser::new();
    println!("{}", parser);
    let s = "a+b";
    let tokens = tokenize_line(s);
    let mut tb = TokenBlock::new(tokens, vec![], (0, 0));
    let obj = parser.obj(&mut tb);
    println!("{}", obj.unwrap());
}

fn try_parse_obj() {
    let parser = Parser::new();
    println!("{}", parser);
    let s = "a+b";
    let tokens = tokenize_line(s);
    let mut tb = TokenBlock::new(tokens, vec![], (0, 0));
    let obj = parser.obj(&mut tb);
    println!("{}", obj.unwrap());
}

fn try_parse_fact() {
    let parser = Parser::new();
    println!("{}", parser);
    let s = "a+b=0";
    let tokens = tokenize_line(s);
    let mut tb = TokenBlock::new(tokens, vec![], (0, 0));
    let fact = parser.fact(&mut tb);
    println!("{}", fact.unwrap());
}

fn try_parse_statements() {
    let parser = Parser::new();
    println!("{}", parser);
    let s = "a+b=0";
    let tokens = tokenize_line(s);
    let mut tb = TokenBlock::new(tokens, vec![], (0, 0));
    let stmt = parser.stmt(&mut tb);
    println!("{}", stmt.unwrap());
}

fn try_executor() {
    let mut module_manager = ModuleManager::new();
    let environment: Box<Environment> = Box::new(Environment::new(HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new()));
    let builtin_environment: Box<Environment> = Box::new(Environment::new(HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new()));
    let mut runtime_context = RuntimeContext::new(&mut module_manager, vec![environment], builtin_environment, HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new());
    let executor = Executor::new(&mut runtime_context);
    println!("{}", executor.line_file_index_string(1, 0));
}

fn try_pipeline() {
    let s = "a+b=0";
    let result = pipeline::run_source_code(s);
    println!("{}", result);
}


fn try_calculate() {
    let one = Obj::Number(Number::new("1"));
    let two = Obj::Number(Number::new("2"));
    let one_add_two = Obj::Add(Add::new(one, two, true));
    println!("{}", one_add_two.calculate_to_string());
}

fn try_obj_well_defined<'a>() {
    let mut module_manager = ModuleManager::new();
    let environment: Box<Environment> = Box::new(Environment::new_empty_env());
    let builtin_environment: Box<Environment> = Box::new(Environment::new_empty_env());
    let mut runtime_context = RuntimeContext::new(&mut module_manager, vec![environment], builtin_environment, HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new());
    let mut executor = Executor::new(&mut runtime_context);
    
    let one = Obj::Number(Number::new("1"));
    let two = Obj::Number(Number::new("2"));
    let one_add_two = Obj::Add(Add::new(one, two, true));
    let atomic_fact = AtomicFact::EqualFact(EqualFact::new(one_add_two, Obj::Number(Number::new("3")), Some((1, 0))));
    println!("{}", atomic_fact);

    let fact = Fact::AtomicFact(atomic_fact);
    let mut verify_state = VerifyState::new(0, false);
    let fact_well_defined = executor.verify_fact_well_defined(&fact, &mut verify_state);
    if fact_well_defined.is_err() {
        println!("ERROR:{}", fact_well_defined.err().unwrap());
    }

    let result = executor.fact(&fact, &mut verify_state);
    if result.is_err() {
        println!("ERROR:{}", result.err().unwrap());
    }
}

fn try_verify_state() {
    let mut verify_state = VerifyState::new(0, false);
    assert!(!verify_state.is_final_round());
    verify_state = verify_state.new_state_with_round_increased();
    assert!(!verify_state.is_final_round());
    verify_state = verify_state.new_state_with_req_ok_set_to_true();
    assert!(verify_state.is_final_round());
}