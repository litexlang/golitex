use super::tokenize_line;
use super::TokenBlock;
use crate::environment::Environment;
use crate::execute::Runtime;
use crate::module_manager::ModuleManager;
use crate::runtime::RuntimeContext;

#[test]
#[ignore]
fn test_fact() {
    let mut module_manager = ModuleManager::new_empty_module_manager("test");
    let mut builtin_environment = Environment::new_empty_env();
    let mut runtime_context = RuntimeContext::new_empty_runtime_context_with_one_env(
        &mut module_manager,
        &mut builtin_environment,
    );
    let mut runtime = Runtime::new(&mut runtime_context);
    let code = "1 + 1 = 2";
    let blocks = TokenBlock::parse_blocks(code, 0).expect("parse blocks failed");
    for mut b in blocks {
        let stmt = runtime.parse_stmt(&mut b);
        match stmt {
            Ok(s) => println!("{}\n", s),
            Err(e) => println!("{}", e),
        }
    }
    println!("success! :)\n");
}

#[test]
fn test_list_set_comma() {
    let mut module_manager = ModuleManager::new_empty_module_manager("test");
    let mut builtin_environment = Environment::new_empty_env();
    let mut runtime_context = RuntimeContext::new_empty_runtime_context_with_one_env(
        &mut module_manager,
        &mut builtin_environment,
    );
    let mut runtime = Runtime::new(&mut runtime_context);
    let mut tb = TokenBlock::new(tokenize_line("{1, 0, 2}"), vec![], (1, 0));
    let r = runtime.parse_obj(&mut tb);
    match r {
        Ok(o) => assert_eq!(o.to_string(), "{1, 0, 2}"),
        Err(e) => panic!("parse {{1, 0, 2}} failed: {:?}", e),
    }
}

#[test]
fn test_list_set_space() {
    let mut module_manager = ModuleManager::new_empty_module_manager("test");
    let mut builtin_environment = Environment::new_empty_env();
    let mut runtime_context = RuntimeContext::new_empty_runtime_context_with_one_env(
        &mut module_manager,
        &mut builtin_environment,
    );
    let mut runtime = Runtime::new(&mut runtime_context);
    let mut tb = TokenBlock::new(tokenize_line("{a b c}"), vec![], (1, 0));
    let r = runtime.parse_obj(&mut tb);
    match r {
        Ok(o) => assert_eq!(o.to_string(), "{a, b, c}"),
        Err(e) => panic!("parse {{a b c}} failed: {:?}", e),
    }
}

#[test]
#[ignore]
fn test_obj() {
    let objs = vec![
        // Number
        "0",
        "42",
        "3.14",
        // AtomWithoutModName
        "x",
        // AtomWithModName
        "M.x",
        // FnObj
        "p(a, b)",
        // Add, Sub, Mul, Div, Mod, Pow（算术）
        "1 + 1",
        "5 - 3",
        "2 * 3",
        "6 / 2",
        "7 % 4",
        "2 ^ (10*20)",
        "1 + 2 * 3",
        "2 + 10 * (f(a)[0]- 10) ^ 2 ^ 3 - 19",
        // Union, Intersect, SetMinus, DisjointUnion, Proj, Range, ClosedRange（前缀 keyword(args)）
        "union(A, B)",
        "intersect(A, B)",
        "set_minus(A, B)",
        "disjoint_union(A, B)",
        "proj(S, 0)",
        "range(0, 1)",
        "closed_range(0, 1)",
        // Cup, Cap, PowerSet, Choose（前缀单参）
        "cup(S)",
        "cap(T)",
        "power_set(S)",
        "choose(S)",
        // TupleDim（前缀单参）
        "tuple_dim(S)",
        // CartDim, Count, Val
        "cart_dim(S)",
        "count(S)",
        "val(x)",
        // Cart, ListSet, FnSetWithoutDom（ListSet 如 "{a b c}" 解析递归较深，可单独测）
        "cart(R, R)",
        // "{a b c}",  // ListSet
        "fn(R, R) R",
        // 单符号集合
        "N_pos",
        "N",
        "Q",
        "Z",
        "R",
        "Q_pos",
        "Z_pos",
        "R_pos",
        "Q_neg",
        "Z_neg",
        "R_neg",
        "Q_nz",
        "Z_nz",
        "R_nz",
        "a[0]",
        "f(1)[0]",
        "&Foo(R)",
        "{1, 0, 2}",
        "fn(x R, y R: x < y)R",
        "{z R: exist a R st {a > z}, z = 10 or $p(z), 1 $in R or $in(a, R)}",
        "M.x.y.z",
        "1 \\pkg::a 2",
        "1 \\pkg::a.b 2",
    ];

    let mut module_manager = ModuleManager::new_empty_module_manager("test");
    let mut builtin_environment = Environment::new_empty_env();
    let mut runtime_context = RuntimeContext::new_empty_runtime_context_with_one_env(
        &mut module_manager,
        &mut builtin_environment,
    );
    let mut runtime = Runtime::new(&mut runtime_context);
    for obj in objs {
        let mut tb = TokenBlock::new(tokenize_line(obj), vec![], (1, 0));
        let result = runtime.parse_obj(&mut tb);
        match result {
            Ok(o) => println!("{}\n", o),
            Err(e) => println!("{}", e),
        }
    }
    println!("success! :)\n");
}
