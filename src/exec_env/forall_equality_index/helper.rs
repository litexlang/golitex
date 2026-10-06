use crate::ast::names::AtomicName;
use crate::ast::obj::*;
use crate::exec_env::ObjIR;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::{
    corresponding_arg_pairs, fn_obj_prefix_obj,
};
use crate::rational_expression::exact_complex::exact_complex_coordinates;
use crate::rational_expression::exact_radical::ExactRadical;
use crate::rational_expression::exact_rational::EvalRational;
use crate::rational_expression::{
    evaluate_obj_to_normalized_decimal_number, is_closed_numeric_expr,
};
use crate::runtime::IdentifierId;
use std::collections::HashSet;
use std::mem::{discriminant, Discriminant};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum Constructor {
    Application(usize),
    Literal(Discriminant<Literal>),
    StandardSet(Discriminant<StandardSet>),
    Arithmetic(Discriminant<ArithmeticOperator>),
    Integer(Discriminant<IntegerOperator>),
    Trig(Discriminant<TrigOperator>),
    ExpLog(Discriminant<ExpLogOperator>),
    Complex(Discriminant<ComplexOperator>),
    SetOperator(Discriminant<SetOperator>),
    SetFormer(Discriminant<SetFormer>),
    Product(Discriminant<ProductShape>),
    FunctionSpace(Discriminant<FunctionSpace>),
    Iterated(Discriminant<IteratedOperator>),
    FiniteSet(Discriminant<FiniteSetStat>),
    StructType(AtomicName),
    Field(Vec<String>),
    Template(AtomicName),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum IdentifierKey {
    Plain(IdentifierId),
    Export(usize, String),
    Module(usize, usize, String),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum Token {
    Parameter,
    Identifier(IdentifierKey),
    Number(String),
    ClosedDecimal(String),
    ClosedReal(ObjIR),
    ClosedComplex(ObjIR, ObjIR),
    Node(Constructor, usize),
    RigidNode(Constructor, usize),
}

pub(super) fn append_pattern(
    object: &Obj,
    parameters: &HashSet<IdentifierId>,
    seen: &mut HashSet<IdentifierId>,
    out: &mut Vec<Token>,
    instantiated_skips: &mut Vec<(usize, usize)>,
) {
    if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = object {
        if parameters.contains(id) {
            seen.insert(*id);
            out.push(Token::Parameter);
            return;
        }
    }
    let (mut token, children) = object_view(object);
    let mut free = HashSet::new();
    crate::instantiate::collect_free_plain_ids(object, &HashSet::new(), &mut free);
    let dependencies: HashSet<_> = free.intersection(parameters).copied().collect();
    if let Token::Node(constructor, arity) = &token {
        if dependencies.is_empty() {
            token = Token::RigidNode(constructor.clone(), *arity);
        }
    }
    // The real matcher can instantiate an already-bound expression when its
    // constructor differs from the goal (e.g. f(t)=t+1 applied to f(1)=2).
    // Store a shared continuation, without enumerating combinations of skips.
    let skip = !children.is_empty() && !dependencies.is_empty() && dependencies.is_subset(seen);
    let start = out.len();
    out.push(token);
    // The certificate matcher peels all shared FnObj suffix groups, visiting
    // their arguments outermost first after the fixed head. The index uses
    // nested application layers instead. Conservatively allow child fallback
    // for parameters anywhere in this application; actual binding remains in
    // the matcher, so this adds candidates without inventing substitutions.
    if matches!(object, Obj::FnObj(_)) {
        seen.extend(dependencies.iter().copied());
    }
    for child in children {
        append_pattern(&child, parameters, seen, out, instantiated_skips);
    }
    if skip {
        instantiated_skips.push((start, out.len()));
    }
    // Opaque binder branches can infer free parameters in the real matcher.
    seen.extend(dependencies);
}

pub(super) fn object_view(object: &Obj) -> (Token, Vec<Obj>) {
    if let Some(value) = closed_value_key(object) {
        return (value, Vec::new());
    }
    structural_view(object)
}

pub(super) fn object_views(object: &Obj) -> Vec<(Token, Vec<Obj>)> {
    let structure = structural_view(object);
    let mut views = vec![structure];
    if let Some(value) = closed_value_key(object) {
        if views[0].0 != value {
            views.push((value, Vec::new()));
        }
    }
    views
}

pub(super) fn structural_view(object: &Obj) -> (Token, Vec<Obj>) {
    if let Obj::Identifier(identifier) = object {
        let key = match identifier {
            IdentifierObj::Plain { id, .. } => IdentifierKey::Plain(*id),
            IdentifierObj::WithExportFileId {
                export_file_id,
                name,
            } => IdentifierKey::Export(*export_file_id, name.clone()),
            IdentifierObj::WithModAndExportFileId {
                global_mod_id,
                export_file_id,
                name,
            } => IdentifierKey::Module(*global_mod_id, *export_file_id, name.clone()),
        };
        return (Token::Identifier(key), Vec::new());
    }
    if let Obj::Literal(Literal::Number(number)) = object {
        return (Token::Number(number.normalized_value.clone()), Vec::new());
    }
    let constructor = match object {
        Obj::Identifier(_) => unreachable!("identifier handled above"),
        Obj::FnObj(value) => Constructor::Application(value.body.last().map_or(0, Vec::len)),
        Obj::Literal(value) => Constructor::Literal(discriminant(value)),
        Obj::StandardSet(value) => Constructor::StandardSet(discriminant(value)),
        Obj::ArithmeticOperator(value) => Constructor::Arithmetic(discriminant(value)),
        Obj::IntegerOperator(value) => Constructor::Integer(discriminant(value)),
        Obj::TrigOperator(value) => Constructor::Trig(discriminant(value)),
        Obj::ExpLogOperator(value) => Constructor::ExpLog(discriminant(value)),
        Obj::ComplexOperator(value) => Constructor::Complex(discriminant(value)),
        Obj::SetOperator(value) => Constructor::SetOperator(discriminant(value)),
        Obj::SetFormer(value) => Constructor::SetFormer(discriminant(value)),
        Obj::ProductShape(value) => Constructor::Product(discriminant(value)),
        Obj::FunctionSpace(value) => Constructor::FunctionSpace(discriminant(value)),
        Obj::IteratedOperator(value) => Constructor::Iterated(discriminant(value)),
        Obj::FiniteSetStat(value) => Constructor::FiniteSet(discriminant(value)),
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(value)) => {
            Constructor::StructType(value.name.clone())
        }
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(value)) => {
            Constructor::Field(value.fields.clone())
        }
        Obj::InstantiatedTemplateObj(value) => Constructor::Template(value.template_name.clone()),
    };
    let children = structural_children(object);
    (Token::Node(constructor, children.len()), children)
}

pub(super) fn contains_binder(object: &Obj) -> bool {
    if matches!(
        object,
        Obj::FunctionSpace(FunctionSpace::FnSet(_) | FunctionSpace::AnonymousFn(_))
            | Obj::SetFormer(SetFormer::SetBuilder(_))
    ) {
        return true;
    }
    structural_children(object).iter().any(contains_binder)
}

fn structural_children(object: &Obj) -> Vec<Obj> {
    if let Obj::FnObj(value) = object {
        let Some(last) = value.body.last() else {
            return Vec::new();
        };
        let mut children = vec![fn_obj_prefix_obj(value, value.body.len() - 1)];
        children.extend(last.iter().map(|arg| arg.as_ref().clone()));
        return children;
    }
    if let Obj::InstantiatedTemplateObj(value) = object {
        return value.args.clone();
    }
    // Binder objects stay conservative opaque branches. The actual matcher
    // performs free-parameter inference and complete alpha/capture checks.
    corresponding_arg_pairs(object, object)
        .unwrap_or_default()
        .into_iter()
        .map(|(left, _)| left)
        .collect()
}

fn closed_value_key(object: &Obj) -> Option<Token> {
    // Follow the Direct calculation leaf's decimal-first order, including
    // exact decimal values beyond the i128 rational evaluator's range.
    if is_closed_numeric_expr(object) {
        if let Some(number) = evaluate_obj_to_normalized_decimal_number(object) {
            return Some(
                match EvalRational::from_obj(&Obj::Literal(Literal::Number(number.clone()))) {
                    Some(value) => Token::ClosedReal(value.to_obj().ir()),
                    None => Token::ClosedDecimal(number.normalized_value),
                },
            );
        }
    }
    if let Some(value) = EvalRational::from_obj(object) {
        return Some(Token::ClosedReal(value.to_obj().ir()));
    }
    if let Some(value) = ExactRadical::from_obj(object) {
        let normalized = value.to_obj();
        return Some(Token::ClosedReal(
            EvalRational::from_obj(&normalized)
                .map_or_else(|| normalized.ir(), |value| value.to_obj().ir()),
        ));
    }
    let (real, imaginary) = exact_complex_coordinates(object)?;
    if imaginary == EvalRational::new(0, 1)? {
        return Some(Token::ClosedReal(real.to_obj().ir()));
    }
    Some(Token::ClosedComplex(
        real.to_obj().ir(),
        imaginary.to_obj().ir(),
    ))
}
