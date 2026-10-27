use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_equivalence_class(
        &self,
        fact: &EqualFact,
        proof: &EqualFactSearchedProofByEquivalenceClass,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match proof {
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path) => {
                self.compile_equality_path(&fact.left, &fact.right, path, position)
            }
            EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(proof) => {
                let resolved = self.resolve_fact(proof.cited.fact_id, position)?;
                if resolved != Fact::AtomicFact(AtomicFact::EqualFact(proof.cited.clone())) {
                    return Err(LeanCompileError::new(
                        "Equality/AlphaCitation",
                        "Alpha endpoint evidence changes its cited source equality.",
                    ));
                }
                let (left, right) = if proof.reversed {
                    (&proof.cited.right, &proof.cited.left)
                } else {
                    (&proof.cited.left, &proof.cited.right)
                };
                let cited =
                    self.compile_registered_equality(proof.cited.fact_id, left, right, position)?;
                let left_identity =
                    self.compile_identity(left, &fact.left, &proof.left_identity, position)?;
                let right_identity =
                    self.compile_identity(right, &fact.right, &proof.right_identity, position)?;
                // Alpha proofs can be tactic terms. Supplying Eq's arguments
                // gives them an expected equality type before elaboration;
                // field notation on an untyped `(by ...)` does not.
                Ok(format!(
                    "(Eq.trans (Eq.symm {left_identity}) (Eq.trans {cited} {right_identity}))"
                ))
            }
            EqualFactSearchedProofByEquivalenceClass::AlphaPaths(proof) => {
                let left_path = self.compile_equality_path(
                    &fact.left,
                    &proof.left,
                    &proof.left_path,
                    position,
                )?;
                let identity =
                    self.compile_identity(&proof.left, &proof.right, &proof.identity, position)?;
                let right_path = self.compile_equality_path(
                    &proof.right,
                    &fact.right,
                    &proof.right_path,
                    position,
                )?;
                Ok(format!(
                    "(Eq.trans {left_path} (Eq.trans {identity} {right_path}))"
                ))
            }
            EqualFactSearchedProofByEquivalenceClass::ViaPeers(proof) => {
                let bindings = self.compile_equal_wd_locals(
                    &proof.bridge.fact,
                    &proof.bridge.well_defined_proof,
                    position,
                )?;
                let locals = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualWDLocals(&proof.bridge.well_defined_proof, 2),
                    2,
                );
                let position = &locals;
                let left_path = self.compile_equality_path(
                    &fact.left,
                    &proof.bridge.fact.left,
                    &proof.left_path,
                    position,
                )?;
                let bridge = self.compile_equality_search_with_parent_wd(
                    &proof.bridge.fact,
                    &proof.bridge.searched_proof,
                    Some(&proof.bridge.well_defined_proof),
                    position,
                )?;
                let right_path = self.compile_equality_path(
                    &proof.bridge.fact.right,
                    &fact.right,
                    &proof.right_path,
                    position,
                )?;
                let proposition = format!(
                    "Litex.Same {} {}",
                    self.compile_object_reference(&fact.left, position)?,
                    self.compile_object_reference(&fact.right, position)?
                );
                Ok(Self::scope_equal_wd_proof(
                    proposition,
                    format!("(Eq.trans {left_path} (Eq.trans {bridge} {right_path}))"),
                    &bindings,
                ))
            }
        }
    }

    pub(in crate::compile_to_lean) fn compile_equality_path(
        &self,
        left: &Obj,
        right: &Obj,
        proof: &KnownEqualityPathProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let mut current = left;
        self.compile_object_reference(left, position)?;
        let mut compiled: Option<String> = None;
        self.compile_object_reference(right, position)?;
        for (from, to, id) in &proof.path {
            if from.ir() != current.ir() {
                return Err(LeanCompileError::new(
                    "Equality/PathOrder",
                    "An equality edge does not continue the recorded ordered path.",
                ));
            }
            let step = self.compile_registered_equality(*id, from, to, position)?;
            compiled = Some(match compiled {
                Some(previous) => format!("(({previous}).trans {step})"),
                None => step,
            });
            current = to;
        }
        if current.ir() != right.ir() {
            return Err(LeanCompileError::new(
                "Equality/PathEndpoint",
                &format!(
                    "The recorded equality path from `{}` ends at `{}`, not the requested `{}`.",
                    left.readable_string(),
                    current.readable_string(),
                    right.readable_string()
                ),
            ));
        }
        // A nonempty path starts with its actual first cited equality. An empty
        // path is reflexivity; infer the semantic value from the expected Eq
        // instead of embedding the entire certified object again.
        Ok(compiled.unwrap_or_else(|| "(show @Eq M.Value _ _ from Eq.refl _)".to_string()))
    }

    pub(in crate::compile_to_lean) fn compile_registered_equality(
        &self,
        id: FactId,
        from: &Obj,
        to: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let resolved = self.resolve_fact(id, position)?;
        let equality = match &resolved {
            Fact::AtomicFact(AtomicFact::EqualFact(equal)) if equal.fact_id == id => equal,
            _ => {
                return Err(LeanCompileError::new(
                    "Equality/PathCitation",
                    "The equality path cites another fact family or identity.",
                ))
            }
        };
        let registered = self.cited_fact_reference(id, position)?;
        if *registered.0 != resolved {
            return Err(LeanCompileError::new(
                "Equality/PathProducer",
                "The cited equality differs from its active compiled producer.",
            ));
        }
        self.compile_object_reference(from, position)?;
        self.compile_object_reference(to, position)?;
        if equality.left.ir() == from.ir() && equality.right.ir() == to.ir() {
            Ok(registered.1.clone())
        } else if equality.right.ir() == from.ir() && equality.left.ir() == to.ir() {
            Ok(format!("({}).symm", registered.1))
        } else {
            Err(LeanCompileError::new(
                "Equality/PathSubject",
                "The cited equality does not prove the recorded oriented edge.",
            ))
        }
    }
}
