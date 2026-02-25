mod arithmetic;
mod consts;
mod errors;
mod helper;
mod obj;
mod predicate;
mod stmt;
mod parameter_set;
mod atom;
use atom::{AtomWithoutPkg, AtomWithPkg, Atom};
use obj::{Obj};
use stmt::Stmt;
use parameter_set::ParameterSet;


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
}

fn try_atom_fn_obj() {
    let a_add_b = Obj::box_fn_obj(Obj::box_atom_without_pkg("+"), vec![Obj::box_atom_without_pkg("a"), Obj::box_atom_without_pkg("b")]);
    println!("{}", a_add_b);

    let a_add_b_with_pkg = Obj::box_fn_obj(Obj::box_atom_with_pkg("PkgA", "name_a"), vec![Obj::box_atom_without_pkg("a"), Obj::box_atom_without_pkg("b")]);
    println!("{}", a_add_b_with_pkg);
}

fn try_arithmetic() {
    let number_one = Obj::box_number("1");
    let number_two = Obj::box_number("2");
    let one_add_two_result = Obj::box_add(number_one, number_two, true);
    let one_sub_two_result = Obj::box_sub(Obj::box_number("1"), Obj::box_number("2"), true);
    let one_mul_two_result = Obj::box_mul(Obj::box_number("1"), Obj::box_number("2"), true);
    let one_div_two_result = Obj::box_div(Obj::box_number("1"), Obj::box_number("2"), true);
    let one_mod_two_result = Obj::box_mod(Obj::box_number("1"), Obj::box_number("2"), true);
    let one_pow_two_result = Obj::box_pow(Obj::box_number("1"), Obj::box_number("2"), true);
    println!("{}, {}, {}, {}, {}, {}",  one_add_two_result, one_sub_two_result, one_mul_two_result, one_div_two_result, one_mod_two_result, one_pow_two_result);   
    println!("{}", one_add_two_result.calculate().unwrap());
    println!("{}", one_sub_two_result.calculate().unwrap());
    println!("{}", one_mul_two_result.calculate().unwrap());
    println!("{}", one_div_two_result.calculate().unwrap());
    println!("{}", one_mod_two_result.calculate().unwrap());
    println!("{}", one_pow_two_result.calculate().unwrap());
}

fn try_set_operations() {
    let union_result = Obj::box_union(Obj::box_atom_without_pkg("A"), Obj::box_atom_without_pkg("B"));
    let intersect_result = Obj::box_intersect(Obj::box_atom_without_pkg("A"), Obj::box_atom_without_pkg("B"));
    let set_minus_result = Obj::box_set_minus(Obj::box_atom_without_pkg("A"), Obj::box_atom_without_pkg("B"));
    let disjoint_union_result = Obj::box_disjoint_union(Obj::box_atom_without_pkg("A"), Obj::box_atom_without_pkg("B"));
    let cup_result = Obj::box_cup(Obj::box_atom_without_pkg("A"));
    let cap_result = Obj::box_cap(Obj::box_atom_without_pkg("A"), Obj::box_atom_without_pkg("B"));
    println!("{}, {}, {}, {}, {}, {}", union_result, intersect_result, set_minus_result, disjoint_union_result, cup_result, cap_result);
}

fn try_stmt() {
    let body3 = vec![Obj::box_atom_without_pkg("a"), Obj::box_atom_without_pkg("b")];
    let stmt = Stmt::box_fact(Atom::box_atom_without_pkg(AtomWithoutPkg::new("name_a")), body3);
    println!("{}", stmt.to_string());

    let body2 = vec![Obj::box_atom_without_pkg("a"), Obj::box_atom_without_pkg("b")];
        let fact2 = Stmt::box_fact(Atom::box_atom_with_pkg(AtomWithPkg::new("pkg_a", "name_a")), body2);
    println!("{}", fact2.to_string());
    
}

fn try_equal_literally() {
    let a = Obj::box_atom_without_pkg("a");
    let b = Obj::box_atom_without_pkg("b");
    println!("{}", Obj::equal_literally(&a, &b));
    let a2 = Obj::box_atom_without_pkg("a");
    println!("{}", Obj::equal_literally(&a2, &a));
}

fn try_list_set() {
    let list_set = Obj::box_list_set(vec![Obj::box_atom_without_pkg("a"), Obj::box_atom_without_pkg("b")]);
    println!("{}", list_set);
}

fn try_set_builder() {
    let set_builder = Obj::box_set_builder();
    println!("{}", set_builder);
}

fn try_fn_set_without_params() {
    let fn_set_without_params = Obj::box_fn_set_without_params(vec![Obj::box_atom_without_pkg("a"), Obj::box_atom_without_pkg("b")], Obj::box_atom_without_pkg("c"));
    println!("{}", fn_set_without_params);
}

fn try_fn_set_with_params() {
    let fn_set_with_params = Obj::box_fn_set_with_params();
    println!("{}", fn_set_with_params);
}

fn try_n_pos_obj() {
    let n_pos_obj = Obj::box_n_pos_obj();
    println!("{}", n_pos_obj);
    let n_obj = Obj::box_n_obj();
    println!("{}", n_obj);
    let q_obj = Obj::box_q_obj();
    println!("{}", q_obj);
    let z_obj = Obj::box_z_obj();
    println!("{}", z_obj);
    let r_obj = Obj::box_r_obj();
    println!("{}", r_obj);
}

fn try_parameter_set() {
    let parameter_set = ParameterSet::box_set();
    println!("{}", parameter_set);
    let nonempty_parameter_set = ParameterSet::box_nonempty_set();
    println!("{}", nonempty_parameter_set);
    let finite_parameter_set = ParameterSet::box_finite_set();
    println!("{}", finite_parameter_set);
    let obj_parameter_set = ParameterSet::box_obj(Obj::box_atom_without_pkg("a"));
    println!("{}", obj_parameter_set);
}

fn try_instantiated_set_template_obj() {
    let instantiated_set_template_obj = Obj::box_inst_set_template_obj(
        Atom::box_atom_with_pkg(AtomWithPkg::new("PkgA", "name_a")),
        vec![Obj::box_atom_without_pkg("b")],
    );
    println!("{}", instantiated_set_template_obj);

    let instantiated_set_template_obj2 = Obj::box_inst_set_template_obj(
        Atom::box_atom_without_pkg(AtomWithoutPkg::new("a")),
        vec![],
    );
    println!("{}", instantiated_set_template_obj2);
}


fn try_cart_set_dim_proj_dim_tuple() {
    let cart = Obj::box_cart(vec![Obj::box_atom_without_pkg("a"), Obj::box_atom_without_pkg("b")]);
    let set_dim = Obj::box_set_dim(Obj::box_atom_without_pkg("a"));
    let proj = Obj::box_proj(Obj::box_atom_without_pkg("a"), Obj::box_atom_without_pkg("b"));
    let dim = Obj::box_dim(Obj::box_atom_without_pkg("b"));
    println!("{}", cart);
    println!("{}", set_dim);
    println!("{}", proj);
    println!("{}", dim);
    let tuple = Obj::box_tuple(vec![Obj::box_atom_without_pkg("a"), Obj::box_atom_without_pkg("b")]);
    println!("{}", tuple);
}

fn try_count_range_closed_range_val() {
    let count = Obj::box_count(Obj::box_atom_without_pkg("a"));
    let range = Obj::box_range(Obj::box_atom_without_pkg("a"), Obj::box_atom_without_pkg("b"));
    let closed_range = Obj::box_closed_range(Obj::box_atom_without_pkg("a"), Obj::box_atom_without_pkg("b"));
    let val = Obj::box_val(Obj::box_atom_without_pkg("a"));
    println!("{}", count);
    println!("{}", range);
    println!("{}", closed_range);
    println!("{}", val);
}