//! Real supremum/infimum constructors consume the source's exact selection evidence.
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::BoundOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_real_extremum_equality(
        &self,
        fact: &EqualFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_real_bounds::RealBoundEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_real_bounds::RealBoundEqualityProof;
        let name = match proof {
            RealBoundEqualityProof::Supremum(_) => "supremum",
            RealBoundEqualityProof::Infimum(_) => "infimum",
        };
        let AtomicFact::NormalAtomicFact(c) = &proof.candidate().fact else {
            return Err(invalid("EqualityCertificate"));
        };
        let selected = |o: &Obj| match o {
            Obj::BoundOperator(BoundOperator::Supremum(a)) => {
                name == "supremum" && certificate_matches(c, name, &a.set)
            }
            Obj::BoundOperator(BoundOperator::Infimum(a)) => {
                name == "infimum" && certificate_matches(c, name, &a.set)
            }
            _ => false,
        };
        let reverse = if selected(&fact.left) {
            false
        } else if selected(&fact.right) {
            true
        } else {
            return Err(invalid("EqualitySubject"));
        };
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
            proof.candidate().searched_proof.as_ref()
        else {
            return Err(invalid("EqualityRoute"));
        };
        let certificate = self.compile_known_atomic(known, &proof.candidate().fact, position)?;
        let obligation = EqualFact {
            fact_id: fact.fact_id,
            left: c.body[1].clone(),
            right: if reverse {
                fact.left.clone()
            } else {
                fact.right.clone()
            },
            line_file: None,
        };
        let equality =
            self.compile_equality_search(&obligation, proof.value_equality(), position)?;
        let set = self.compile_object_reference(&c.body[0], position)?;
        let value = self.compile_object_reference(&c.body[1], position)?;
        let term = format!(
            "(Eq.trans (Litex.{name}Value_eq_certificate {set} {value} {certificate}) {equality})"
        );
        Ok(if reverse {
            format!("(Eq.symm {term})")
        } else {
            term
        })
    }

    pub(super) fn compile_real_extremum_congruence(
        &self,
        fact: &EqualFact,
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (name, left, right) = match (&fact.left, &fact.right) {
            (
                Obj::BoundOperator(BoundOperator::Supremum(a)),
                Obj::BoundOperator(BoundOperator::Supremum(b)),
            ) => ("supremum", a.set.as_ref(), b.set.as_ref()),
            (
                Obj::BoundOperator(BoundOperator::Infimum(a)),
                Obj::BoundOperator(BoundOperator::Infimum(b)),
            ) => ("infimum", a.set.as_ref(), b.set.as_ref()),
            _ => return Err(invalid("CongruenceOperator")),
        };
        let [child] = children else {
            return Err(invalid("CongruenceArity"));
        };
        if !matches!(source_subject(child)?,Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir()==left.ir() && f.right.ir()==right.ir())
        {
            return Err(invalid("CongruenceSubject"));
        }
        let prior = SourcePosition::new(
            Some(position),
            super::source_position::SourceOwner::EqualityRequirements(children),
            0,
        );
        Ok(format!(
            "(congrArg (Litex.{name}Value (M := M)) {})",
            self.compile_verify(child, &prior)?.1
        ))
    }

    pub(super) fn compile_real_extremum_wd(
        &self,
        object: &BoundOperator,
        proof: &BoundOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (name, set, set_wd, real_set, selection) = match (object, proof) {
            (BoundOperator::Supremum(a), BoundOperatorObjWellDefinedProofByDef::Supremum(p)) => (
                "supremum",
                a.set.as_ref(),
                p.set_wd.as_ref(),
                p.real_set.as_ref(),
                p.selection.as_ref(),
            ),
            (BoundOperator::Infimum(a), BoundOperatorObjWellDefinedProofByDef::Infimum(p)) => (
                "infimum",
                a.set.as_ref(),
                p.set_wd.as_ref(),
                p.real_set.as_ref(),
                p.selection.as_ref(),
            ),
            _ => return Err(invalid("WDConstructor")),
        };
        ensure_object(set, set_wd)?;
        if !is_real_subset(&source_subject(real_set)?, set) {
            return Err(invalid("RealCarrier"));
        }
        let set_term = self.compile_wd(
            set_wd,
            &SourcePosition {
                before: 0,
                ..*position
            },
        )?;
        let real_term = self.compile_wd_requirement(
            real_set,
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;
        let prior = SourcePosition {
            before: 2,
            ..*position
        };
        let subject = source_subject(selection)?;
        let proof = self.compile_wd_requirement(selection, &prior)?;
        let existence = match &subject {
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(c))
                if certificate_matches(c, name, set) =>
            {
                let formed = super::source_position::SourcePosition::new(
                    Some(&prior),
                    super::source_position::SourceOwner::Verify(selection),
                    2,
                );
                let value = self.compile_object_reference(&c.body[1], &formed)?;
                let title = if name == "supremum" {
                    "Supremum"
                } else {
                    "Infimum"
                };
                format!("(Litex.real{title}ExistsOfCertificate {set_term} {value} {proof})")
            }
            _ => {
                validate_extremum_existence(&subject, name, set)?;
                proof
            }
        };
        Ok(format!("(Litex.{name} {set_term} {real_term} {existence})"))
    }
}

pub(super) fn certificate_name(predicate: &AtomicName) -> Option<&'static str> {
    let AtomicName::Plain { name } = predicate else {
        return None;
    };
    match name.as_str() {
        "is_real_least_upper_bound" => Some("RealLeastUpperBound"),
        "is_real_greatest_lower_bound" => Some("RealGreatestLowerBound"),
        _ => None,
    }
}
pub(super) fn certificate_matches(c: &NormalAtomicFact, name: &str, set: &Obj) -> bool {
    certificate_name(&c.predicate)
        == Some(if name == "supremum" {
            "RealLeastUpperBound"
        } else {
            "RealGreatestLowerBound"
        })
        && c.body.len() == 2
        && c.body[0].ir() == set.ir()
}
pub(super) fn is_real_subset(fact: &Fact, set: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::SubsetFact(f)) if f.left.ir()==set.ir() && f.right==Obj::StandardSet(StandardSet::R))
}
pub(super) fn validate_extremum_existence(
    fact: &Fact,
    name: &str,
    set: &Obj,
) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(f) = fact else {
        return Err(invalid("Existence"));
    };
    let [g] = f.typed_parameters.groups.as_slice() else {
        return Err(invalid("ExistenceBinder"));
    };
    let [p] = g.params.as_slice() else {
        return Err(invalid("ExistenceBinder"));
    };
    let [QuantifierFreeFact::AtomicFact(AtomicFact::NormalAtomicFact(c))] = f.facts.as_slice()
    else {
        return Err(invalid("ExistenceBody"));
    };
    let mut free = std::collections::HashSet::new();
    crate::instantiate::collect_free_plain_ids(set, &std::collections::HashSet::new(), &mut free);
    if !matches!(
        &g.param_type,
        ParamType::Obj(Obj::StandardSet(StandardSet::R))
    ) || !certificate_matches(c, name, set)
        || !matches!(&c.body[1],Obj::Identifier(IdentifierObj::Plain { id,.. }) if *id==p.id)
        || free.contains(&p.id)
    {
        return Err(invalid("ExistenceContract"));
    }
    Ok(())
}
pub(super) fn bound_stages(
    proof: &ObjWellDefinedProof,
) -> Option<(&ObjWellDefinedProof, &VerifyFactResult, &VerifyFactResult)> {
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::BoundOperator(p),
        ..
    } = proof
    else {
        return None;
    };
    Some(match p {
        BoundOperatorObjWellDefinedProofByDef::Supremum(p) => {
            (&p.set_wd, &p.real_set, &p.selection)
        }
        BoundOperatorObjWellDefinedProofByDef::Infimum(p) => (&p.set_wd, &p.real_set, &p.selection),
    })
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(
        &format!("RealExtremum/{stage}"),
        "Extremum evidence differs in its source set, real carrier, direction or candidate.",
    )
}
