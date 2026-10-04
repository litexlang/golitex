//! Reserved theorem applications, separate from ordinary proof search.
use super::helper::*;
use super::{intersection, membership, real_analysis, sums};
use crate::ast::fact::Fact;
use crate::ast::obj::*;
use crate::ast::param::*;
use crate::ast::stmt::{TheoremCall, TheoremCallArguments};
use crate::ast::names::AtomicName;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::exec_by_thm_stmt::PreparedRelease;
use crate::execute::execute_by_stmt::result::{BuiltinThmApplication, ExecReleaseThmStmtFailed};
use crate::runtime::{Runtime, RuntimeResult};

pub(in crate::execute::execute_by_stmt) fn prepare_builtin_thm(
    rt: &mut Runtime, call: &TheoremCall,
) -> RuntimeResult<Option<Result<PreparedRelease, ExecReleaseThmStmtFailed>>> {
    let Some(id) = BuiltinTheoremId::from_name(call.name.local_name()) else { return Ok(None); };
    if !matches!(call.name, AtomicName::Plain { .. }) {
        return Ok(Some(Err(ExecReleaseThmStmtFailed::Shape(format!("builtin theorem `{id}` is a reserved bare global name")))));
    }
    let args = match &call.arguments {
        TheoremCallArguments::Parenthesized(args) if args.len() == id.arity() => args,
        arguments => {
            let actual = match arguments { TheoremCallArguments::Bare => 0, TheoremCallArguments::Parenthesized(args) => args.len() };
            return Ok(Some(Err(ExecReleaseThmStmtFailed::BuiltinArity { theorem: id, expected: id.arity(), actual })));
        }
    };
    let prepared = match prepare_contract(rt, id, args)? {
        Ok((requirements, conclusions)) => Ok(PreparedRelease {
            type_facts: vec![], dom_facts: requirements.clone(), conclusions: conclusions.clone(),
            builtin: Some(BuiltinThmApplication { theorem: id, arguments: args.clone(), requirements, conclusions }),
        }),
        Err(message) => Err(ExecReleaseThmStmtFailed::BuiltinShape { theorem: id, message }),
    };
    Ok(Some(prepared))
}

fn prepare_contract(rt: &mut Runtime, id: BuiltinTheoremId, args: &[Obj]) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    let a = args[0].clone();
    let result = match id {
        // A ⊆ B and B finite implies A finite; no finiteness premise on A.
        SubsetOfFiniteSetIsFinite => {
            let b = args[1].clone();
            let requirements = vec![is_set(rt, a.clone()).into(), finite(rt, b.clone()).into(), subset(rt, a.clone(), b).into()];
            Ok((requirements, vec![finite(rt, a).into()]))
        }
        FiniteSetHasBijectiveIndex => {
            let requirement = finite(rt, a.clone()).into();
            let index = rt.fresh_internal_param();
            let index_obj = identifier(&index);
            let length = size(a.clone());
            let domain = range(number("1"), length.clone());
            let sequence = Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet { set: Box::new(a.clone()), n: Box::new(length) }));
            let body = bijective(rt, domain, a, index_obj);
            let conclusion = exist(rt, typed(index, sequence), vec![body], false);
            Ok((vec![requirement], vec![conclusion]))
        }
        RationalHasUniqueReducedFraction => {
            let requirement = atomic_in(rt, a.clone(), Obj::StandardSet(StandardSet::Q)).into();
            let p = rt.fresh_internal_param();
            let d = rt.fresh_internal_param();
            let p_obj = identifier(&p);
            let d_obj = identifier(&d);
            let ratio = Obj::ArithmeticOperator(ArithmeticOperator::Div(Div { left: Box::new(p_obj.clone()), right: Box::new(d_obj.clone()) }));
            let gcd = Obj::IntegerOperator(IntegerOperator::Gcd(Gcd { left: Box::new(p_obj), right: Box::new(d_obj) }));
            let body = vec![equal(rt, a, ratio), equal(rt, gcd, number("1"))];
            let params = TypedParameterList { groups: vec![
                TypedParameterGroup { params: vec![p], param_type: ParamType::Obj(Obj::StandardSet(StandardSet::Z)) },
                TypedParameterGroup { params: vec![d], param_type: ParamType::Obj(Obj::StandardSet(StandardSet::NPos)) },
            ] };
            Ok((vec![requirement], vec![exist(rt, params, body, true)]))
        }
        FunctionSetMember | SetBuilderMember | DefinedSetMember | StructMember
        | CartesianMemberFromCoordinates | IndexCartesianMember
        | IndexCartesianNonemptyByChoiceFromFamily | IndexCartesianNonemptyByChoiceFromPointwise
        | TupleEqualFromCoordinates => membership::prepare_membership(rt, id, args)?,
        FamilyIntersectionMember | FamilyIntersectionMemberFacts | IndexedIntersectionMember => {
            intersection::prepare_intersection(rt, id, args)
        }
        SumLessEqualFromPointwise | FiniteSetSumLessEqualFromPointwise
        | FiniteSetSummandLessEqualSum | FiniteSetSumSubstitution
        | SumOverBijectiveFiniteSetEnumerations => sums::prepare_sums(rt, id, args)?,
        _ => real_analysis::prepare_real_analysis(rt, id, args),
    };
    Ok(result)
}
