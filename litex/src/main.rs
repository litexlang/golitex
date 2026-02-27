mod arithmetic;
mod consts;
mod errors;
mod helper;
mod obj;
mod stmt;
mod parameter_set;
mod atom;
mod atomic_fact;
mod fact;
mod exist_fact;
mod or_fact;
mod forall_fact;
mod reversible_fact;
mod specific_fact;
mod forall_fact_with_iff;
mod and_fact;
mod and_fact_or_specific_fact;
use and_fact::AndFact;
use and_fact_or_specific_fact::AndFactOrSpecFact;
use atom::{AtomWithoutPkg, AtomWithPkg, Atom};
use obj::{
    Obj, FnObj, Number, Add, Sub, Mul, Div, Mod, Pow,
    Union, Intersect, SetMinus, DisjointUnion, Cup, Cap,
    ListSet, SetBuilder, FnSetWithoutParams, FnSetWithParams,
    NPosObj, NObj, QObj, ZObj, RObj, InstSetTemplateObj,
    Cart, SetDim, Proj, Dim, Tuple, Count, Range, ClosedRange, Val, PowerSet, Choice,
};
use parameter_set::{ParameterSet, SetAsParamSet, NonemptySetAsParamSet, FiniteSetAsParamSet};
use stmt::{Stmt};
use atomic_fact::{InFact, NotInFact,IsCartFact, NotIsCartFact, IsTupleFact, NotIsTupleFact, AtomicFact, NormalAtomicFact, NotNormalAtomicFact, EqualFact, NotEqualFact,
    LessFact, NotLessFact, GreaterFact, NotGreaterFact,
    LessEqualFact, NotLessEqualFact, GreaterEqualFact, NotGreaterEqualFact,
    IsSetFact, NotIsSetFact, IsNonemptySetFact, NotIsNonemptySetFact,
    IsFiniteSetFact, NotIsFiniteSetFact,
};
use exist_fact::{ExistFact, TrueExistFact, NotExistFact};
use specific_fact::SpecFact;
use or_fact::OrFact;
use forall_fact::ForallFact;
use forall_fact_with_iff::ForallFactWithIff;
use fact::Fact;
use errors::{ArithmeticErr, Err};

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
    try_instantiated_set_template_obj();
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
}

fn try_atom_fn_obj() {
    let a_add_b = Obj::FnObj(FnObj::new(
        Obj::AtomWithoutPkg(AtomWithoutPkg::new("+")),
        vec![
            Obj::AtomWithoutPkg(AtomWithoutPkg::new("a")),
            Obj::AtomWithoutPkg(AtomWithoutPkg::new("b")),
        ],
    ));
    println!("{}", a_add_b);

    let a_add_b_with_pkg = Obj::FnObj(FnObj::new(
        Obj::AtomWithPkg(AtomWithPkg::new("PkgA", "name_a")),
        vec![
            Obj::AtomWithoutPkg(AtomWithoutPkg::new("a")),
            Obj::AtomWithoutPkg(AtomWithoutPkg::new("b")),
        ],
    ));
    println!("{}", a_add_b_with_pkg);
}

fn try_arithmetic() {
    let number_one = Obj::Number(Number::new("1"));
    let number_two = Obj::Number(Number::new("2"));
    let one_add_two_result = Obj::Add(Add::new(number_one, number_two, true));
    let one_sub_two_result = Obj::Sub(Sub::new(Obj::Number(Number::new("1")), Obj::Number(Number::new("2")), true));
    let one_mul_two_result = Obj::Mul(Mul::new(Obj::Number(Number::new("1")), Obj::Number(Number::new("2")), true));
    let one_div_two_result = Obj::Div(Div::new(Obj::Number(Number::new("1")), Obj::Number(Number::new("2")), true));
    let one_mod_two_result = Obj::Mod(Mod::new(Obj::Number(Number::new("1")), Obj::Number(Number::new("2")), true));
    let one_pow_two_result = Obj::Pow(Pow::new(Obj::Number(Number::new("1")), Obj::Number(Number::new("2")), true));
    println!("{}, {}, {}, {}, {}, {}",  one_add_two_result, one_sub_two_result, one_mul_two_result, one_div_two_result, one_mod_two_result, one_pow_two_result);
    println!("{}", one_add_two_result.calculate().unwrap());
    println!("{}", one_sub_two_result.calculate().unwrap());
    println!("{}", one_mul_two_result.calculate().unwrap());
    println!("{}", one_div_two_result.calculate().unwrap());
    println!("{}", one_mod_two_result.calculate().unwrap());
    println!("{}", one_pow_two_result.calculate().unwrap());
}

fn try_set_operations() {
    let mk = |s: &str| Obj::AtomWithoutPkg(AtomWithoutPkg::new(s));
    let union_result = Obj::Union(Union::new(mk("A"), mk("B")));
    let intersect_result = Obj::Intersect(Intersect::new(mk("A"), mk("B")));
    let set_minus_result = Obj::SetMinus(SetMinus::new(mk("A"), mk("B")));
    let disjoint_union_result = Obj::DisjointUnion(DisjointUnion::new(mk("A"), mk("B")));
    let cup_result = Obj::Cup(Cup::new(mk("A")));
    let cap_result = Obj::Cap(Cap::new(mk("A"), mk("B")));
    println!("{}, {}, {}, {}, {}, {}", union_result, intersect_result, set_minus_result, disjoint_union_result, cup_result, cap_result);
}

fn try_stmt() {
    let body3 = vec![
        Obj::AtomWithoutPkg(AtomWithoutPkg::new("a")),
        Obj::AtomWithoutPkg(AtomWithoutPkg::new("b")),
    ];
    let fact1 = Stmt::Fact(Fact::AtomicFact(AtomicFact::NormalAtomicFact(NormalAtomicFact::new(
        Atom::AtomWithoutPkg(AtomWithoutPkg::new("p")),
        body3,
        1,
        0,
    ))));
    println!("{}", fact1.to_string());

    let body2 = vec![
        Obj::AtomWithoutPkg(AtomWithoutPkg::new("a")),
        Obj::AtomWithoutPkg(AtomWithoutPkg::new("b")),
    ];
    let fact2 = Stmt::Fact(Fact::AtomicFact(AtomicFact::NormalAtomicFact(NormalAtomicFact::new(
        Atom::AtomWithPkg(AtomWithPkg::new("PkgA", "name_a")),
        body2,
        1,
        0,
    ))));
    println!("{}", fact2.to_string());
}

fn try_equal_literally() {
    let a = Obj::AtomWithoutPkg(AtomWithoutPkg::new("a"));
    let b = Obj::AtomWithoutPkg(AtomWithoutPkg::new("b"));
    println!("{}", Obj::equal_literally(&a, &b));
    let a2 = Obj::AtomWithoutPkg(AtomWithoutPkg::new("a"));
    println!("{}", Obj::equal_literally(&a2, &a));
}

fn try_list_set() {
    let list_set = Obj::ListSet(ListSet::new(vec![
        Obj::AtomWithoutPkg(AtomWithoutPkg::new("a")),
        Obj::AtomWithoutPkg(AtomWithoutPkg::new("b")),
    ]));
    println!("{}", list_set);
}

fn try_set_builder() {
    let set_builder = Obj::SetBuilder(SetBuilder::new());
    println!("{}", set_builder);
}

fn try_fn_set_without_params() {
    let fn_set_without_params = Obj::FnSetWithoutParams(FnSetWithoutParams::new(
        vec![
            Obj::AtomWithoutPkg(AtomWithoutPkg::new("a")),
            Obj::AtomWithoutPkg(AtomWithoutPkg::new("b")),
        ],
        Obj::AtomWithoutPkg(AtomWithoutPkg::new("c")),
    ));
    println!("{}", fn_set_without_params);
}

fn try_fn_set_with_params() {
    let fn_set_with_params = Obj::FnSetWithParams(FnSetWithParams::new());
    println!("{}", fn_set_with_params);
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
}

fn try_parameter_set() {
    let parameter_set = ParameterSet::Set(SetAsParamSet::new());
    println!("{}", parameter_set);
    let nonempty_parameter_set = ParameterSet::NonemptySet(NonemptySetAsParamSet::new());
    println!("{}", nonempty_parameter_set);
    let finite_parameter_set = ParameterSet::FiniteSet(FiniteSetAsParamSet::new());
    println!("{}", finite_parameter_set);
    let obj_parameter_set = ParameterSet::Obj(Obj::AtomWithoutPkg(AtomWithoutPkg::new("a")));
    println!("{}", obj_parameter_set);
}

fn try_instantiated_set_template_obj() {
    let instantiated_set_template_obj = Obj::InstSetTemplateObj(InstSetTemplateObj::new(
        Atom::AtomWithPkg(AtomWithPkg::new("PkgA", "name_a")),
        vec![Obj::AtomWithoutPkg(AtomWithoutPkg::new("b"))],
    ));
    println!("{}", instantiated_set_template_obj);

    let instantiated_set_template_obj2 = Obj::InstSetTemplateObj(InstSetTemplateObj::new(
        Atom::AtomWithoutPkg(AtomWithoutPkg::new("a")),
        vec![],
    ));
    println!("{}", instantiated_set_template_obj2);
}


fn try_cart_set_dim_proj_dim_tuple() {
    let mk = |s: &str| Obj::AtomWithoutPkg(AtomWithoutPkg::new(s));
    let cart = Obj::Cart(Cart::new(vec![mk("a"), mk("b")]));
    let set_dim = Obj::SetDim(SetDim::new(mk("a")));
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
    let mk = |s: &str| Obj::AtomWithoutPkg(AtomWithoutPkg::new(s));
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
    let mk = |s: &str| Obj::AtomWithoutPkg(AtomWithoutPkg::new(s));
    let power_set = Obj::PowerSet(PowerSet::new(mk("a")));
    let choice = Obj::Choice(Choice::new(mk("a"), mk("b")));
    println!("{}", power_set);
    println!("{}", choice);
}

fn try_atomic_fact() {
    let line = 1u32;
    let _normal = AtomicFact::NormalAtomicFact(NormalAtomicFact::new(
        Atom::AtomWithoutPkg(AtomWithoutPkg::new("p")),
        vec![Obj::mk("a"), Obj::mk("b")],
        line,
        0,
    ));
    let _equal = AtomicFact::EqualFact(EqualFact::new(Obj::mk("x"), Obj::mk("y"), line, 0));
    let _less = AtomicFact::LessFact(LessFact::new(Obj::mk("a"), Obj::mk("b"), line, 0));
    let _greater = AtomicFact::GreaterFact(GreaterFact::new(Obj::mk("a"), Obj::mk("b"), line, 0));
    let _less_equal = AtomicFact::LessEqualFact(LessEqualFact::new(Obj::mk("a"), Obj::mk("b"), line, 0));
    let _greater_equal = AtomicFact::GreaterEqualFact(GreaterEqualFact::new(Obj::mk("a"), Obj::mk("b"), line, 0));
    let _is_set = AtomicFact::IsSetFact(IsSetFact::new(Obj::mk("S"), line, 0));
    let _is_nonempty_set = AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(Obj::mk("S"), line, 0));
    let _is_finite_set = AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(Obj::mk("S"), line, 0));
    let _is_cart = AtomicFact::IsCartFact(IsCartFact::new(Obj::mk("S"), line, 0));
    let _not_is_cart = AtomicFact::NotIsCartFact(NotIsCartFact::new(Obj::mk("S"), line, 0));

    let _not_normal = AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact::new(
        Atom::AtomWithoutPkg(AtomWithoutPkg::new("p")),
        vec![Obj::mk("a")],
        line,
        0,
    ));
    let _not_equal = AtomicFact::NotEqualFact(NotEqualFact::new(Obj::mk("x"), Obj::mk("y"), line, 0));
    let _not_less = AtomicFact::NotLessFact(NotLessFact::new(Obj::mk("a"), Obj::mk("b"), line, 0));
    let _not_greater = AtomicFact::NotGreaterFact(NotGreaterFact::new(Obj::mk("a"), Obj::mk("b"), line, 0));
    let _not_less_equal = AtomicFact::NotLessEqualFact(NotLessEqualFact::new(Obj::mk("a"), Obj::mk("b"), line, 0));
    let _not_greater_equal = AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact::new(Obj::mk("a"), Obj::mk("b"), line, 0));
    let _not_is_set = AtomicFact::NotIsSetFact(NotIsSetFact::new(Obj::mk("S"), line, 0));
    let _not_is_nonempty_set = AtomicFact::NotIsNonemptySetFact(NotIsNonemptySetFact::new(Obj::mk("S"), line, 0));
    let _not_is_finite_set = AtomicFact::NotIsFiniteSetFact(NotIsFiniteSetFact::new(Obj::mk("S"), line, 0));
    println!("{}", _normal.str_with_line_file());
    println!("{}", _equal.str_with_line_file());
    println!("{}", _less.str_with_line_file());
    println!("{}", _greater.str_with_line_file());
    println!("{}", _less_equal.str_with_line_file());
    println!("{}", _greater_equal.str_with_line_file());
    println!("{}", _is_set.str_with_line_file());
    println!("{}", _is_nonempty_set.str_with_line_file());
    println!("{}", _is_finite_set.str_with_line_file());
    println!("{}", _not_normal.str_with_line_file());
    println!("{}", _not_equal.str_with_line_file());
    println!("{}", _not_less.str_with_line_file());
    println!("{}", _not_greater.str_with_line_file());
    println!("{}", _not_less_equal.str_with_line_file());
    println!("{}", _not_greater_equal.str_with_line_file());
    println!("{}", _not_is_set.str_with_line_file());
    println!("{}", _not_is_nonempty_set.str_with_line_file());
    println!("{}", _not_is_finite_set.str_with_line_file());
    println!("{}", _is_cart.str_with_line_file());
    println!("{}", _not_is_cart.str_with_line_file());

    let _in = AtomicFact::InFact(InFact::new(Obj::mk("a"), Obj::mk("S"), line, 0));
    let _not_in = AtomicFact::NotInFact(NotInFact::new(Obj::mk("a"), Obj::mk("S"), line, 0));
    println!("{}", _in.str_with_line_file());
    println!("{}", _not_in.str_with_line_file());

    let _is_tuple = AtomicFact::IsTupleFact(IsTupleFact::new(Obj::mk("t"), line, 0));
    let _not_is_tuple = AtomicFact::NotIsTupleFact(NotIsTupleFact::new(Obj::mk("t"), line, 0));
    println!("{}", _is_tuple.str_with_line_file());
    println!("{}", _not_is_tuple.str_with_line_file());
}

fn try_exist_fact() {
    let af1 = vec![AtomicFact::EqualFact(EqualFact::new(Obj::mk("a"), Obj::mk("b"), 1, 0))];
    let _true_exist = ExistFact::TrueExistFact(TrueExistFact::new(
        vec!["x".to_string()],
        vec![ParameterSet::Set(SetAsParamSet::new())],
        af1,
        1,
        0,
    ));
    let af2 = vec![AtomicFact::EqualFact(EqualFact::new(Obj::mk("a"), Obj::mk("b"), 1, 0))];
    let _not_exist = ExistFact::NotExistFact(NotExistFact::new(
        vec!["y".to_string()],
        vec![ParameterSet::Set(SetAsParamSet::new())],
        af2,
        2,
        0,
    ));
    println!("{}", _true_exist.str_with_line_file());
    println!("{}", _not_exist.str_with_line_file());
}

fn try_spec_fact() {
    let _spec_atom = SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(Obj::mk("a"), Obj::mk("b"), 1, 0)));
    let ef = ExistFact::TrueExistFact(TrueExistFact::new(
        vec![],
        vec![],
        vec![AtomicFact::EqualFact(EqualFact::new(Obj::mk("u"), Obj::mk("v"), 1, 0))],
        1,
        0,
    ));
    let _spec_exist = SpecFact::ExistFact(ef);
    println!("{}", _spec_atom.str_with_line_file());
    println!("{}", _spec_exist.str_with_line_file());
}

fn try_or_fact() {
    let facts = vec![
        AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            Obj::mk("p"),
            Obj::mk("q"),
            1,
            0,
        )))),
    ];
    let _or = OrFact::new(facts, 1, 0);
    println!("{}", _or.str_with_line_file());

    let facts2 = vec![
        AndFactOrSpecFact::AndFact(AndFact::new(vec![], 1, 0)),
        AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            Obj::mk("p"),
            Obj::mk("q"),
            1,
            0,
        )))),
    ];
    let _or2 = OrFact::new(facts2, 1, 0);
    println!("{}", _or2.str_with_line_file());
}

fn try_and_fact_or_spec_fact() {
    let _spec = AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
        Obj::mk("a"),
        Obj::mk("b"),
        1,
        0,
    ))));
    println!("{}", _spec.str_with_line_file());

    let facts = vec![
        SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            Obj::mk("p"),
            Obj::mk("q"),
            1,
            0,
        ))),
        SpecFact::AtomicFact(AtomicFact::LessFact(LessFact::new(
            Obj::mk("x"),
            Obj::mk("y"),
            2,
            0,
        ))),
    ];
    let _and = AndFactOrSpecFact::AndFact(AndFact::new(facts, 1, 0));
    println!("{}", _and.str_with_line_file());
}

fn try_forall_fact() {
    let _forall = ForallFact::new(
        vec!["n".to_string()],
        vec![ParameterSet::Set(SetAsParamSet::new())],
        vec![],
        vec![SpecFact::AtomicFact(AtomicFact::EqualFact(
            EqualFact::new(Obj::mk("a"), Obj::mk("b"), 1, 0),
        ))],
        1,
        0,
    );

    println!("{}", _forall.str_with_line_file());
}

fn try_forall_fact_with_iff() {
    let forall = ForallFact::new(
        vec!["n".to_string()],
        vec![ParameterSet::Set(SetAsParamSet::new())],
        vec![SpecFact::AtomicFact(AtomicFact::EqualFact(
            EqualFact::new(Obj::mk("a"), Obj::mk("b"), 1, 0),
        ))],
        vec![SpecFact::AtomicFact(AtomicFact::EqualFact(
            EqualFact::new(Obj::mk("a"), Obj::mk("b"), 1, 0),
        ))],
        1,
        0,
    );

    let _forall_fact_with_iff = ForallFactWithIff::new(forall, vec![SpecFact::AtomicFact(AtomicFact::EqualFact(
        EqualFact::new(Obj::mk("a"), Obj::mk("b"), 1, 0),
    ))], 2, 0);
    println!("{}", _forall_fact_with_iff.str_with_line_file());
}


fn try_fact() {
    let af = AtomicFact::EqualFact(EqualFact::new(Obj::mk("a"), Obj::mk("b"), 1, 0));
    let _f_atom = Fact::AtomicFact(af);
    let ef = ExistFact::TrueExistFact(TrueExistFact::new(
        vec![],
        vec![],
        vec![AtomicFact::EqualFact(EqualFact::new(Obj::mk("u"), Obj::mk("v"), 1, 0))],
        1,
        0,
    ));
    let _f_exist = Fact::ExistFact(ef);
    let _f_or = Fact::OrFact(OrFact::new(vec![], 1, 0));
    let _f_forall = Fact::ForallFact(ForallFact::new(
        vec![],
        vec![],
        vec![],
        vec![],
        1,
        0,
    ));
    let forall = ForallFact::new(vec![], vec![], vec![], vec![], 1, 0);
    let _f_forall_fact_with_iff = Fact::ForallFactWithIff(ForallFactWithIff::new(
        forall,
        vec![],
        1,
        0,
    ));

    let facts = vec![
        SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            Obj::mk("p"),
            Obj::mk("q"),
            1,
            0,
        ))),
    ];
    let _f_and = Fact::AndFact(AndFact::new(facts, 1, 0));
    println!("{}", _f_and.str_with_line_file());
}

fn try_errors() {
    let _err = ArithmeticErr::new("demo");

    println!("{}", _err);

    let err: Err = Err::ArithmeticErr(ArithmeticErr::new("demo"));
    println!("{}", err);
}

fn try_and_fact() {
    let facts = vec![
        SpecFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            Obj::mk("p"),
            Obj::mk("q"),
            1,
            0,
        ))),
    ];
    let _and = AndFact::new(facts, 1, 0);
    println!("{}", _and.str_with_line_file());
}