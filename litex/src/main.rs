mod arithmetic;
mod consts;
mod errors;
mod helper;
mod obj;
mod predicate;
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
mod chain_fact;
use atom::{AtomWithoutPkg, AtomWithPkg, Atom};
use obj::{
    Obj, FnObj, Number, Add, Sub, Mul, Div, Mod, Pow,
    Union, Intersect, SetMinus, DisjointUnion, Cup, Cap,
    ListSet, SetBuilder, FnSetWithoutParams, FnSetWithParams,
    NPosObj, NObj, QObj, ZObj, RObj, InstSetTemplateObj,
    Cart, SetDim, Proj, Dim, Tuple, Count, Range, ClosedRange, Val, PowerSet, Choice,
};
use parameter_set::{ParameterSet, SetAsParamSet, NonemptySetAsParamSet, FiniteSetAsParamSet};
use stmt::{Stmt, PureSpecFact};

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
}

fn try_atom_fn_obj() {
    let a_add_b = Box::new(Obj::FnObj(FnObj::new(
        Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("+"))),
        vec![
            Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("a"))),
            Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("b"))),
        ],
    )));
    println!("{}", a_add_b);

    let a_add_b_with_pkg = Box::new(Obj::FnObj(FnObj::new(
        Box::new(Obj::AtomWithPkg(AtomWithPkg::new("PkgA", "name_a"))),
        vec![
            Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("a"))),
            Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("b"))),
        ],
    )));
    println!("{}", a_add_b_with_pkg);
}

fn try_arithmetic() {
    let number_one = Box::new(Obj::Number(Number::new("1")));
    let number_two = Box::new(Obj::Number(Number::new("2")));
    let one_add_two_result = Box::new(Obj::Add(Add::new(number_one, number_two, true)));
    let one_sub_two_result = Box::new(Obj::Sub(Sub::new(Box::new(Obj::Number(Number::new("1"))), Box::new(Obj::Number(Number::new("2"))), true)));
    let one_mul_two_result = Box::new(Obj::Mul(Mul::new(Box::new(Obj::Number(Number::new("1"))), Box::new(Obj::Number(Number::new("2"))), true)));
    let one_div_two_result = Box::new(Obj::Div(Div::new(Box::new(Obj::Number(Number::new("1"))), Box::new(Obj::Number(Number::new("2"))), true)));
    let one_mod_two_result = Box::new(Obj::Mod(Mod::new(Box::new(Obj::Number(Number::new("1"))), Box::new(Obj::Number(Number::new("2"))), true)));
    let one_pow_two_result = Box::new(Obj::Pow(Pow::new(Box::new(Obj::Number(Number::new("1"))), Box::new(Obj::Number(Number::new("2"))), true)));
    println!("{}, {}, {}, {}, {}, {}",  one_add_two_result, one_sub_two_result, one_mul_two_result, one_div_two_result, one_mod_two_result, one_pow_two_result);   
    println!("{}", one_add_two_result.calculate().unwrap());
    println!("{}", one_sub_two_result.calculate().unwrap());
    println!("{}", one_mul_two_result.calculate().unwrap());
    println!("{}", one_div_two_result.calculate().unwrap());
    println!("{}", one_mod_two_result.calculate().unwrap());
    println!("{}", one_pow_two_result.calculate().unwrap());
}

fn try_set_operations() {
    let mk = |s: &str| Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new(s)));
    let union_result = Box::new(Obj::Union(Union::new(mk("A"), mk("B"))));
    let intersect_result = Box::new(Obj::Intersect(Intersect::new(mk("A"), mk("B"))));
    let set_minus_result = Box::new(Obj::SetMinus(SetMinus::new(mk("A"), mk("B"))));
    let disjoint_union_result = Box::new(Obj::DisjointUnion(DisjointUnion::new(mk("A"), mk("B"))));
    let cup_result = Box::new(Obj::Cup(Cup::new(mk("A"))));
    let cap_result = Box::new(Obj::Cap(Cap::new(mk("A"), mk("B"))));
    println!("{}, {}, {}, {}, {}, {}", union_result, intersect_result, set_minus_result, disjoint_union_result, cup_result, cap_result);
}

fn try_stmt() {
    let body3 = vec![
        Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("a"))),
        Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("b"))),
    ];
    let stmt = Box::new(Stmt::Fact(PureSpecFact::new(
        Box::new(Atom::AtomWithoutPkg(AtomWithoutPkg::new("name_a"))),
        body3,
    )));
    println!("{}", stmt.to_string());

    let body2 = vec![
        Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("a"))),
        Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("b"))),
    ];
    let fact2 = Box::new(Stmt::Fact(PureSpecFact::new(
        Box::new(Atom::AtomWithPkg(AtomWithPkg::new("pkg_a", "name_a"))),
        body2,
    )));
    println!("{}", fact2.to_string());
}

fn try_equal_literally() {
    let a = Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("a")));
    let b = Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("b")));
    println!("{}", Obj::equal_literally(&a, &b));
    let a2 = Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("a")));
    println!("{}", Obj::equal_literally(&a2, &a));
}

fn try_list_set() {
    let list_set = Box::new(Obj::ListSet(ListSet::new(vec![
        Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("a"))),
        Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("b"))),
    ])));
    println!("{}", list_set);
}

fn try_set_builder() {
    let set_builder = Box::new(Obj::SetBuilder(SetBuilder::new()));
    println!("{}", set_builder);
}

fn try_fn_set_without_params() {
    let fn_set_without_params = Box::new(Obj::FnSetWithoutParams(FnSetWithoutParams::new(
        vec![
            Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("a"))),
            Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("b"))),
        ],
        Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("c"))),
    )));
    println!("{}", fn_set_without_params);
}

fn try_fn_set_with_params() {
    let fn_set_with_params = Box::new(Obj::FnSetWithParams(FnSetWithParams::new()));
    println!("{}", fn_set_with_params);
}

fn try_n_pos_obj() {
    let n_pos_obj = Box::new(Obj::NPosObj(NPosObj::new()));
    println!("{}", n_pos_obj);
    let n_obj = Box::new(Obj::NObj(NObj::new()));
    println!("{}", n_obj);
    let q_obj = Box::new(Obj::QObj(QObj::new()));
    println!("{}", q_obj);
    let z_obj = Box::new(Obj::ZObj(ZObj::new()));
    println!("{}", z_obj);
    let r_obj = Box::new(Obj::RObj(RObj::new()));
    println!("{}", r_obj);
}

fn try_parameter_set() {
    let parameter_set = Box::new(ParameterSet::Set(SetAsParamSet::new()));
    println!("{}", parameter_set);
    let nonempty_parameter_set = Box::new(ParameterSet::NonemptySet(NonemptySetAsParamSet::new()));
    println!("{}", nonempty_parameter_set);
    let finite_parameter_set = Box::new(ParameterSet::FiniteSet(FiniteSetAsParamSet::new()));
    println!("{}", finite_parameter_set);
    let obj_parameter_set = Box::new(ParameterSet::Obj(Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("a")))));
    println!("{}", obj_parameter_set);
}

fn try_instantiated_set_template_obj() {
    let instantiated_set_template_obj = Box::new(Obj::InstSetTemplateObj(InstSetTemplateObj::new(
        Box::new(Atom::AtomWithPkg(AtomWithPkg::new("PkgA", "name_a"))),
        vec![Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new("b")))],
    )));
    println!("{}", instantiated_set_template_obj);

    let instantiated_set_template_obj2 = Box::new(Obj::InstSetTemplateObj(InstSetTemplateObj::new(
        Box::new(Atom::AtomWithoutPkg(AtomWithoutPkg::new("a"))),
        vec![],
    )));
    println!("{}", instantiated_set_template_obj2);
}


fn try_cart_set_dim_proj_dim_tuple() {
    let mk = |s: &str| Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new(s)));
    let cart = Box::new(Obj::Cart(Cart::new(vec![mk("a"), mk("b")])));
    let set_dim = Box::new(Obj::SetDim(SetDim::new(mk("a"))));
    let proj = Box::new(Obj::Proj(Proj::new(mk("a"), mk("b"))));
    let dim = Box::new(Obj::Dim(Dim::new(mk("b"))));
    println!("{}", cart);
    println!("{}", set_dim);
    println!("{}", proj);
    println!("{}", dim);
    let tuple = Box::new(Obj::Tuple(Tuple::new(vec![mk("a"), mk("b")])));
    println!("{}", tuple);
}

fn try_count_range_closed_range_val() {
    let mk = |s: &str| Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new(s)));
    let count = Box::new(Obj::Count(Count::new(mk("a"))));
    let range = Box::new(Obj::Range(Range::new(mk("a"), mk("b"))));
    let closed_range = Box::new(Obj::ClosedRange(ClosedRange::new(mk("a"), mk("b"))));
    let val = Box::new(Obj::Val(Val::new(mk("a"))));
    println!("{}", count);
    println!("{}", range);
    println!("{}", closed_range);
    println!("{}", val);
}

fn try_power_set_choice() {
    let mk = |s: &str| Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new(s)));
    let power_set = Box::new(Obj::PowerSet(PowerSet::new(mk("a"))));
    let choice = Box::new(Obj::Choice(Choice::new(mk("a"), mk("b"))));
    println!("{}", power_set);
    println!("{}", choice);
}