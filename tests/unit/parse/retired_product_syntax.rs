//! Retired syntax and payloads cannot bypass current exact-function contracts.
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval { code: String::new(), session: false, strict: true, language })
}

#[test]
fn retired_product_surface_rejects_before_execution_and_keeps_existing_binding_scope() {
    for (source, diagnostic) in [
        ("tuple_dim(p)=2", "tuple_dim is removed"),
        ("proj(cart(R,Z),1)=R", "proj is removed"),
        ("p[1]=1", "object indexing with [] is removed"),
        ("p[1][2]=1", "object indexing with [] is removed"),
        ("$is_tuple(p)", "is_tuple` is removed"),
        ("not $is_tuple(p)", "is_tuple` is removed"),
        ("not not $is_tuple(p)", "is_tuple` is removed"),
        ("$is_cart(cart(R,Z))", "is_cart` is removed"),
        ("not $is_cart(cart(R,Z))", "is_cart` is removed"),
        ("cart_dim(cart(R,Z))=2", "cart_dim is removed"),
    ] {
        let mut rt=runtime(OutputLanguage::English);
        assert!(rt.run_litex_code("have p cart(R,Z)=(1,2)").unwrap().success);
        let before=rt.top_exec_env().facts.facts_by_id.len();
        let run=rt.run_litex_code(source).unwrap();
        assert!(!run.success && run.session_error.is_some(), "old surface accepted: {source}");
        assert!(format!("{:?}",run.session_error).contains(diagnostic), "wrong diagnostic: {source}");
        assert_eq!(rt.top_exec_env().facts.facts_by_id.len(),before);
        assert!(rt.run_litex_code("p(1)=1\np(2) $in Z").unwrap().success);
        assert!(!rt.run_litex_code("2=3").unwrap().success);
    }
    let mut rt=runtime(OutputLanguage::English);
    assert!(!rt.run_litex_code("let picked=tuple_dim((1,2))").unwrap().success);
    assert!(rt.run_litex_code("have picked R=1\npicked=1").unwrap().success,
        "retired RHS left its attempted binding in parse scope");
}

#[test]
fn new_coordinate_calls_reconstruction_intervals_and_generic_indexed_families_remain_available() {
    let mut rt=runtime(OutputLanguage::English);
    let run=rt.run_litex_code("have p cart(R,Z)\np=(p(1),p(2))\np(1) $in R\np(2) $in Z\n2 $in closed_range(1,2)\n0 $in '[0,1]\ncart()={()}\nlet family=fn(k {1}) power_set(R) {{0}}\nindex_cart({1},power_set(R),family)=index_cart({1},power_set(R),family)\n").unwrap();
    assert!(run.success && run.session_error.is_none(), "{:?}",run.session_error);
    for false_goal in ["p(3)=0","p=(p(2),p(1))","p=(p(1),p(1),p(2))"] {
        assert!(!rt.run_litex_code(false_goal).unwrap().success,"{false_goal}");
    }
}

#[test]
fn retired_product_payloads_fail_even_when_old_object_wd_is_recorded() {
    use crate::ast::obj::{Cart,CartDim,Literal,Number,Obj,ObjAtIndex,ProductShape,Proj,StandardSet,Tuple,TupleDim};
    use crate::execute::execute_fact_stmt::VerifyState;
    let number=|n:&str|Obj::Literal(Literal::Number(Number{normalized_value:n.into()}));
    let tuple=Obj::ProductShape(ProductShape::Tuple(Tuple{args:vec![Box::new(number("1")),Box::new(number("2"))]}));
    let cart=Obj::ProductShape(ProductShape::Cart(Cart{args:vec![Box::new(Obj::StandardSet(StandardSet::R)),Box::new(Obj::StandardSet(StandardSet::Z))]}));
    for obj in [
        Obj::ProductShape(ProductShape::CartDim(CartDim{set:Box::new(cart.clone())})),
        Obj::ProductShape(ProductShape::TupleDim(TupleDim{arg:Box::new(tuple.clone())})),
        Obj::ProductShape(ProductShape::Proj(Proj{set:Box::new(cart),dim:Box::new(number("1"))})),
        Obj::ProductShape(ProductShape::ObjAtIndex(ObjAtIndex{obj:Box::new(tuple),index:Box::new(number("1"))})),
    ] {
        let mut rt=runtime(OutputLanguage::English);
        let old_id=rt.global_ids.allocate_well_definedness_id();
        // Existing memory API seeds a stale entry; no state contract is changed.
        rt.top_exec_env_mut().well_defined_objects.record(obj.clone(),old_id);
        assert!(rt.verify_obj_well_definedness(&obj,VerifyState::top_level()).unwrap().is_failed(),
            "old cache revived a retired payload");
        assert!(rt.run_litex_code("1=1").unwrap().success);
    }
}

#[test]
fn retired_shape_predicates_fail_wd_even_when_an_old_fact_is_stored_in_every_language() {
    use crate::ast::fact::{AtomicFact,Fact,IsCartFact,IsTupleFact,NotIsCartFact,NotIsTupleFact};
    use crate::ast::obj::{Cart,Literal,Number,Obj,ProductShape,StandardSet,Tuple};
    use crate::ast::stmt::Stmt;
    for language in OutputLanguage::ALL {
        for index in 0..4 {
            let mut rt=runtime(language);
            let tuple=Obj::ProductShape(ProductShape::Tuple(Tuple{args:vec![Box::new(Obj::Literal(Literal::Number(Number{normalized_value:"1".into()})))]}));
            let cart=Obj::ProductShape(ProductShape::Cart(Cart{args:vec![Box::new(Obj::StandardSet(StandardSet::R))]}));
            let id=rt.global_ids.allocate_fact_id();
            let fact=match index {
                0=>AtomicFact::IsTupleFact(IsTupleFact{fact_id:id,set:tuple,line_file:None}),
                1=>AtomicFact::NotIsTupleFact(NotIsTupleFact{fact_id:id,set:tuple,line_file:None}),
                2=>AtomicFact::IsCartFact(IsCartFact{fact_id:id,set:cart,line_file:None}),
                _=>AtomicFact::NotIsCartFact(NotIsCartFact{fact_id:id,set:cart,line_file:None}),
            };
            // A stale accepted-fact index cannot supply a current signature.
            rt.store_atomic_fact(&fact).unwrap();
            let before=rt.top_exec_env().facts.facts_by_id.len();
            let result=rt.exec_stmt(&Stmt::Fact(Fact::AtomicFact(fact))).unwrap();
            assert!(result.is_failed());
            assert_eq!(rt.top_exec_env().facts.facts_by_id.len(),before);
            let detailed=crate::json_output::project_stmt_detailed(&result,&rt).stringify();
            assert!(detailed.contains("retired_builtin"),"{language:?}: {detailed}");
            crate::knowledge_base::JsonValue::parse(&detailed).unwrap();
        }
    }
}

#[test]
fn coordinate_reader_misses_preserve_general_returns_tuple_beta_and_returned_eta() {
    for source in [
        "have S nonempty_set\nhave f fn(x R) S\nf(2) $in S",
        "have fn pair(x R) cart(R,R)=(x,x)\npair(2)=(2,2)",
        "have fn triple(a,b,c R) cart(R,R,R)=(a,b,c)\ntriple(1,2,3)=(1,2,3)",
        "have abstract_pair fn(x R) cart(R,R)\nabstract_pair(2)=(abstract_pair(2)(1),abstract_pair(2)(2))",
        "have A set=R\nforall p cart(R,A),j closed_range(1,2):\n    p(j) $in A",
    ] {
        let mut rt=runtime(OutputLanguage::English);
        let run=rt.run_litex_code(source).unwrap();
        assert!(run.success && run.session_error.is_none(),"{source}\n{}",
            crate::json_output::emit_run_detailed(&run,&rt,"call-reader-fallthrough",None));
        assert!(!rt.run_litex_code("2=3").unwrap().success);
    }
}
