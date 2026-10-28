use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_composition::{CompositionSignatureProof, CompositionCallableProof};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_composition::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::{compound_objs_alpha_equal,anonymous_fns_alpha_equal};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_composition_equality(
        &self,
        fact: &EqualFact,
        proof: &CompositionEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let CompositionEqualityProof::Associativity(p) = proof {
            let left = Obj::FunctionSpace(FunctionSpace::Composition(p.left.clone()));
            let right = Obj::FunctionSpace(FunctionSpace::Composition(p.right.clone()));
            let reversed = if same(&fact.left, &left) && same(&fact.right, &right) {
                false
            } else if same(&fact.left, &right) && same(&fact.right, &left) {
                true
            } else {
                return Err(LeanCompileError::unsupported("CompositionAssoc/Endpoints"));
            };
            let (
                Obj::FunctionSpace(FunctionSpace::Composition(fg)),
                Obj::FunctionSpace(FunctionSpace::Composition(gh)),
            ) = (p.left.outer.as_ref(), p.right.inner.as_ref())
            else {
                return Err(LeanCompileError::unsupported("CompositionAssoc/Shape"));
            };
            if !same(&fg.outer, &p.right.outer)
                || !same(&fg.inner, &gh.outer)
                || !same(&p.left.inner, &gh.inner)
            {
                return Err(LeanCompileError::unsupported("CompositionAssoc/Operands"));
            }
            let l = self.compile_object_reference(&left, position)?;
            let r = self.compile_object_reference(&right, position)?;
            let eq=format!("(Litex.FunctionSemantics.composition_associative (Litex.composeSpec ({l}).val.outer) (Litex.composeSpec ({r}).val.inner) (Litex.composeSpec {l}) (Litex.composeSpec {r}))");
            return Ok(if reversed { format!("({eq}).symm") } else { eq });
        }
        let selected = [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ]
        .into_iter()
        .find(|(a, b, _)| {
            let Obj::FunctionSpace(FunctionSpace::Composition(c)) = a else {
                return false;
            };
            match proof {
                CompositionEqualityProof::LeftIdentity(_) => same(&c.inner, b),
                CompositionEqualityProof::RightIdentity(_) => same(&c.outer, b),
                CompositionEqualityProof::Definition(p) => same(
                    a,
                    &Obj::FunctionSpace(FunctionSpace::Composition(p.callable.composition.clone())),
                ),
                _ => false,
            }
        })
        .ok_or_else(|| LeanCompileError::unsupported("CompositionLaw/Endpoints"))?;
        let (root, other, reversed) = selected;
        let Obj::FunctionSpace(FunctionSpace::Composition(c)) = root else {
            unreachable!()
        };
        let object = self.compile_object_reference(root, position)?;
        let eq = match proof {
            CompositionEqualityProof::LeftIdentity(p) => {
                validate_identity(&p.identity)?;
                let literal = Obj::FunctionSpace(FunctionSpace::AnonymousFn(p.identity.clone()));
                let identity = self.compile_object_reference(&literal, position)?;
                let path =
                    self.compile_equality_path(&c.outer, &literal, &p.identity_equal, position)?;
                format!("(Litex.composeLeftIdentity {object} {identity} {path} (by intro x; rfl))")
            }
            CompositionEqualityProof::RightIdentity(p) => {
                validate_identity(&p.identity)?;
                let literal = Obj::FunctionSpace(FunctionSpace::AnonymousFn(p.identity.clone()));
                let identity = self.compile_object_reference(&literal, position)?;
                let path =
                    self.compile_equality_path(&c.inner, &literal, &p.identity_equal, position)?;
                let d = &p.full_domain;
                ensure_object(&c.outer, &d.function_wd)?;
                ensure_object(
                    &Obj::FunctionSpace(FunctionSpace::FnSet(d.target.clone())),
                    &d.target_wd,
                )?;
                if d.target != p.identity.body {
                    return Err(LeanCompileError::unsupported(
                        "CompositionRightIdentity/CompleteDomain",
                    ));
                }
                let scope = SourcePosition::new(
                    Some(position),
                    SourceOwner::FunctionDomainWD(d),
                    usize::MAX,
                );
                self.compile_wd(&d.function_wd, &scope)?;
                self.compile_wd(&d.target_wd, &scope)?;
                let s = self.compile_fn_signature(&d.source.signature, &scope)?;
                let hf = self.compile_complete_domain_member(&c.outer, &d.source, &scope)?;
                let (steps, domain_equal) = self.compile_function_domain_match(d, position)?;
                let law = format!("(Litex.composeRightIdentity {object} {identity} {path} (by intro x; rfl) {s} {hf} {domain_equal})");
                if steps.is_empty() {
                    law
                } else {
                    format!(
                        "(by\n  {}\n  exact {law}\n)",
                        steps.join("\n").replace('\n', "\n  ")
                    )
                }
            }
            CompositionEqualityProof::Definition(p) => {
                let mut a = p.callable.function.clone();
                let mut b = p.function.clone();
                a.body.ret_set = Box::new(Obj::StandardSet(StandardSet::R));
                b.body.ret_set = a.body.ret_set.clone();
                if !anonymous_fns_alpha_equal(&a, &b) {
                    return Err(LeanCompileError::unsupported("CompositionDefinition/Body"));
                }
                let literal = Obj::FunctionSpace(FunctionSpace::AnonymousFn(p.function.clone()));
                let function = self.compile_object_reference(&literal, position)?;
                let path =
                    self.compile_equality_path(other, &literal, &p.function_equal, position)?;
                let member = self.compile_composition_member(root, &p.callable, position)?;
                let eq = self.compile_composition_formula_law(
                    root,
                    &p.callable,
                    &function,
                    &p.function,
                    position,
                )?;
                let target = self.compile_object_reference(other, position)?;
                format!("(by\n  have _composition_interface := {member}\n  have _composition_formula : Litex.Same {object} {function} := {eq}\n  exact _composition_formula.trans (show Litex.Same {function} {target} from ({path}).symm))")
            }
            _ => unreachable!(),
        };
        Ok(if reversed { format!("({eq}).symm") } else { eq })
    }

    fn compile_composition_formula_law(
        &self,
        root: &Obj,
        p: &CompositionCallableProof,
        literal: &str,
        function: &AnonymousFn,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match &p.signature {
            CompositionSignatureProof::Interfaces {
                outer_domain,
                inner_domain,
            } => self.compile_composition_formula_interfaces(
                root,
                p,
                literal,
                function,
                outer_domain,
                inner_domain,
                position,
            ),
            CompositionSignatureProof::Construction => position
                .with_visible_wd(root, &mut |wd, producer| {
                    let DetailedObjWellDefinedProof::ByDef {
                        proof:
                            ObjWellDefinedProofByDef::FunctionSpace(
                                FunctionSpaceObjWellDefinedProofByDef::Composition(c),
                            ),
                        ..
                    } = (wd).detailed_ref()
                    else {
                        return Err(LeanCompileError::unsupported(
                            "CompositionDefinition/Constructor",
                        ));
                    };
                    if c.function != p.function {
                        return Err(LeanCompileError::unsupported(
                            "CompositionDefinition/Function",
                        ));
                    }
                    let scope =
                        SourcePosition::new(Some(producer), SourceOwner::WD(wd), usize::MAX);
                    self.compile_composition_formula_interfaces(
                        root,
                        p,
                        literal,
                        function,
                        &c.outer_domain,
                        &c.inner_domain,
                        &scope,
                    )
                })?
                .ok_or_else(|| LeanCompileError::unsupported("CompositionDefinition/Producer")),
        }
    }

    fn compile_composition_formula_interfaces(
        &self,
        root: &Obj,
        p: &CompositionCallableProof,
        literal: &str,
        function: &AnonymousFn,
        outer: &CompleteFunctionDomainProof,
        inner: &CompleteFunctionDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let object = self.compile_object_reference(root, position)?;
        let s = self.compile_fn_signature(&outer.signature, position)?;
        let t = self.compile_fn_signature(&inner.signature, position)?;
        let hf = self.compile_complete_domain_member(&p.composition.outer, outer, position)?;
        let hg = self.compile_complete_domain_member(&p.composition.inner, inner, position)?;
        let arity = function
            .body
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.params.len())
            .sum::<usize>();
        let body = if arity == 1 {
            "(by intro x _; rfl)".to_string()
        } else {
            let (parts, values, _) = self.compile_preimage_domain_parts(
                &inner.signature,
                "_composition_input",
                position,
            )?;
            let repack = self.compile_preimage_repack(&values, "_preimage_base");
            let f = self.compile_object_reference(&p.composition.outer, position)?;
            let g = self.compile_object_reference(&p.composition.inner, position)?;
            format!("(by\n  intro _composition_input _preimage_domain\n  {}\n  have _repack : _composition_input = Litex.FiniteFunction.tupleValue (M := M) ![{}] := {repack}\n  exact congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote {f}) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote {g}) x)) _repack.symm)",parts.join("\n  "),values.join(", "))
        };
        Ok(format!(
            "(Litex.composeEqFormula {object} {literal} {s} {t} {hf} {hg} (by rfl) {body})"
        ))
    }
}

fn same(a: &Obj, b: &Obj) -> bool {
    a == b || compound_objs_alpha_equal(a, b)
}
fn validate_identity(f: &AnonymousFn) -> Result<(), LeanCompileError> {
    let params = f
        .body
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|g| &g.params)
        .collect::<Vec<_>>();
    if params.len() != 1
        || f.equal_to.as_ref() != &Obj::Identifier(IdentifierObj::from_bound_name(params[0]))
    {
        return Err(LeanCompileError::unsupported("CompositionIdentity/Body"));
    }
    Ok(())
}
