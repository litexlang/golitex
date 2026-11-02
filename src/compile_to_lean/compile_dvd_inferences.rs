use super::helper::is_exact_zero;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::InferDvdFactResult;

impl LitexToLeanCompiler {
    pub(super) fn compile_dvd_inferences(
        &self,
        rules: &[InferDvdFactResult],
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::DvdFact(seed)) = seed else {
            return Err(invalid("Seed"));
        };
        let mut lines = Vec::new();
        let mut ids = std::collections::HashSet::new();
        ids.insert(seed.fact_id);
        for (index, rule) in rules.iter().enumerate() {
            let InferDvdFactResult::Definition(p) = rule;
            if p.source_fact_id != seed.fact_id {
                return Err(invalid("SeedIdentity"));
            }
            let StoreFactResult::AtomicFact(remainder) = &p.remainder_zero.store else {
                return Err(invalid("RemainderStore"));
            };
            if !matches!(&remainder.fact,AtomicFact::EqualFact(f) if is_exact_zero(&f.right)
                && matches!(&f.left,Obj::IntegerOperator(IntegerOperator::Mod(m)) if m.left.ir()==seed.left.ir() && m.right.ir()==seed.right.ir()))
            {
                return Err(invalid("RemainderSubject"));
            }
            let StoreFactResult::ExistShapedFact(multiple) = &p.integer_multiple.store else {
                return Err(invalid("MultipleStore"));
            };
            let ExistShapedFact::Exist(multiple) = &multiple.fact else {
                return Err(invalid("MultipleFamily"));
            };
            let [group] = multiple.typed_parameters.groups.as_slice() else {
                return Err(invalid("MultipleBinder"));
            };
            let [parameter] = group.params.as_slice() else {
                return Err(invalid("MultipleBinder"));
            };
            let bound = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
            if group.param_type != ParamType::Obj(Obj::StandardSet(StandardSet::Z))
                || super::compile_real_set_bounds::contains_parameter(&seed.left, parameter.id)
                || super::compile_real_set_bounds::contains_parameter(&seed.right, parameter.id)
                || !matches!(multiple.facts.as_slice(),[QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(f))]
                    if f.left.ir()==seed.left.ir() && matches!(&f.right,Obj::ArithmeticOperator(ArithmeticOperator::Mul(m)) if m.left.ir()==bound.ir() && m.right.ir()==seed.right.ir()))
            {
                return Err(invalid("MultipleSubject"));
            }
            let remainder_fact = Fact::AtomicFact(remainder.fact.clone());
            let multiple_fact = Fact::ExistFact(multiple.clone());
            for (store, fact) in [
                (&p.remainder_zero, &remainder_fact),
                (&p.integer_multiple, &multiple_fact),
            ] {
                self.validate_store(&store.store, fact)?;
                if !ids.insert(fact.fact_id()) {
                    return Err(invalid("PublicationIdentity"));
                }
            }
            let prior = SourcePosition {
                before: 2 * index,
                ..*position
            };
            let first = SourcePosition {
                before: 2 * index + 1,
                ..*position
            };
            let second = SourcePosition {
                before: 2 * index + 2,
                ..*position
            };
            let a = self.compile_object_reference(&seed.left, &prior)?;
            let b = self.compile_object_reference(&seed.right, &prior)?;
            let h = &compiled.1;
            let name = remainder_name(remainder_fact.fact_id());
            let wd = format!("(Litex.dvdConstructorWD {a} {b} {h})");
            lines.push(format!(
                "{} {name}{} := (Litex.mod {a} {b} {wd}.1 {wd}.2.1 {wd}.2.2)",
                if prior.is_local() {
                    "let"
                } else {
                    "noncomputable def"
                },
                if prior.is_local() {
                    String::new()
                } else {
                    self.context_header(&prior)?
                }
            ));
            let reference = if prior.is_local() {
                name
            } else {
                self.context_application(&name, &first)
            };
            let proposition = format!("Litex.Same {reference} (Litex.number (M := M) 0)");
            lines.push(self.emit_internal_fact(
                &remainder_fact,
                &(proposition, format!("(Litex.dvdRemainderZero {a} {b} {h})")),
                &first,
            )?);
            let binder = format!("_value_i{}", parameter.id.value());
            let proposition=format!("∃ ({binder} : Litex.Obj (M := M) M.Value), ∃ (_ : Litex.In {binder} (Litex.Z (M := M))), Litex.denote {a} = M.mulValue (Litex.denote {binder}) (Litex.denote {b})");
            lines.push(self.emit_internal_fact(
                &multiple_fact,
                &(
                    proposition,
                    format!("(Litex.dvdIntegerMultiple {a} {b} {h})"),
                ),
                &second,
            )?);
        }
        Ok(lines)
    }

    pub(super) fn compile_dvd_inferred_subject(
        &self,
        object: &Obj,
        store: &StoreFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let Some(original) = position.dvd_remainder_subject(store) else {
            return Ok(None);
        };
        if original.ir() != object.ir() {
            return Ok(None);
        }
        let seed = match position.owner {
            SourceOwner::AtomicInference(Fact::AtomicFact(AtomicFact::DvdFact(seed)), _) => seed,
            SourceOwner::PropInference(source) => {
                let StoreFactResult::AtomicFact(stored) = &source.store else {
                    return Err(invalid("OriginalOwner"));
                };
                let AtomicFact::DvdFact(seed) = &stored.fact else {
                    return Err(invalid("OriginalOwner"));
                };
                seed
            }
            _ => return Err(invalid("OriginalOwner")),
        };
        // This exact inference owner starts after its primary Dvd store.
        // Use its original scoped seed reference; a proof-local alias cannot
        // occur in the enclosing quantified theorem's declaration type.
        let seed_name = format!("h_{}", seed.fact_id.value());
        let seed_reference = if position.is_local() {
            seed_name
        } else {
            self.context_application(&seed_name, position)
        };
        let a = self.compile_object_reference(&seed.left, position)?;
        let b = self.compile_object_reference(&seed.right, position)?;
        let wd = format!("(Litex.dvdConstructorWD {a} {b} {seed_reference})");
        Ok(Some(format!(
            "(Litex.mod {a} {b} {wd}.1 {wd}.2.1 {wd}.2.2)"
        )))
    }
}
fn remainder_name(id: FactId) -> String {
    format!("_dvd_remainder_h{}", id.value())
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("DvdInference/{part}"))
}
