//! Native contracts for elementary prime / gcd / divisibility theorems.
use super::helper::*;
use crate::ast::fact::{AndChainAtomicFact, AtomicFact, DvdFact, Fact, OrFact, PrimeFact};
use crate::ast::obj::{ArithmeticOperator, Gcd, IntegerOperator, Mul, Obj, Pow, StandardSet};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::runtime::Runtime;

pub(super) fn prepare_number_theory(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> Result<(Vec<Fact>, Vec<Fact>), String> {
    use BuiltinTheoremId::*;
    let integers = Obj::StandardSet(StandardSet::Z);
    match id {
        GcdWithPrimeIsOneOrPrime => {
            let a = args[0].clone();
            let p = args[1].clone();
            let requirements = vec![
                atomic_in(rt, a.clone(), integers).into(),
                atomic_in(rt, p.clone(), Obj::StandardSet(StandardSet::NPos)).into(),
                prime(rt, p.clone()).into(),
            ];
            let gcd = Obj::IntegerOperator(IntegerOperator::Gcd(Gcd {
                left: Box::new(a),
                right: Box::new(p.clone()),
            }));
            let left = equal(rt, gcd.clone(), number("1"));
            let right = equal(rt, gcd, p);
            Ok((requirements, vec![or_two(rt, left, right)]))
        }
        PrimeDividesProduct => {
            let a = args[0].clone();
            let b = args[1].clone();
            let p = args[2].clone();
            let product = mul(a.clone(), b.clone());
            let requirements = vec![
                atomic_in(rt, a.clone(), integers.clone()).into(),
                atomic_in(rt, b.clone(), integers).into(),
                atomic_in(rt, p.clone(), Obj::StandardSet(StandardSet::NPos)).into(),
                prime(rt, p.clone()).into(),
                dvd(rt, product, p.clone()).into(),
            ];
            let left = dvd(rt, a, p.clone());
            let right = dvd(rt, b, p);
            Ok((requirements, vec![or_two(rt, left, right)]))
        }
        PrimeDividesPower => {
            let a = args[0].clone();
            let k = args[1].clone();
            let p = args[2].clone();
            let powered = pow(a.clone(), k.clone());
            let requirements = vec![
                atomic_in(rt, a.clone(), integers).into(),
                atomic_in(rt, k, Obj::StandardSet(StandardSet::NPos)).into(),
                atomic_in(rt, p.clone(), Obj::StandardSet(StandardSet::NPos)).into(),
                prime(rt, p.clone()).into(),
                dvd(rt, powered, p.clone()).into(),
            ];
            Ok((requirements, vec![dvd(rt, a, p).into()]))
        }
        _ => Err(format!("unsupported number-theory builtin theorem `{id}`")),
    }
}

fn prime(rt: &mut Runtime, value: Obj) -> AtomicFact {
    PrimeFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        value,
        line_file: None,
    }
    .into()
}

fn dvd(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    DvdFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}

fn or_two(rt: &mut Runtime, left: AtomicFact, right: AtomicFact) -> Fact {
    Fact::OrFact(OrFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        facts: vec![
            AndChainAtomicFact::AtomicFact(left),
            AndChainAtomicFact::AtomicFact(right),
        ],
        line_file: None,
    })
}

fn mul(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
        left: Box::new(left),
        right: Box::new(right),
    }))
}

fn pow(base: Obj, exponent: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(base),
        exponent: Box::new(exponent),
    }))
}
