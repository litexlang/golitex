use super::compile_function_template::function_guard_fact;
use super::helper::*;
use super::piecewise_evidence::PiecewiseEvidence;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::{
    ExecHaveFnEqualCaseByCaseStmtResult, ExecHaveFnEqualCaseByCaseStmtSuccessResult,
};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(super) fn compile_have_fn_cases_statement(
        &self,
        result: &ExecHaveFnEqualCaseByCaseStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if local {
            return Err(LeanCompileError::unsupported(
                "PiecewiseFunction/LocalDeclaration",
            ));
        }
        let ExecHaveFnEqualCaseByCaseStmtResult::Success(p) = result else {
            return Err(LeanCompileError::unsupported("PiecewiseFunction/Failed"));
        };
        let count = p.statement.cases.len();
        if count == 0
            || p.statement.equal_tos.len() != count
            || p.case_return_checks.len() != count
            || p.disjoint.len() != count * (count - 1) / 2
        {
            return Err(LeanCompileError::unsupported(
                "PiecewiseFunction/CaseCapture",
            ));
        }
        let signature = piecewise_signature(p);
        let set = Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone()));
        let formed_set = format!(
            "(show Litex.Obj (M := M) (Litex.FunctionSignature M) from {})",
            self.compile_wd(success_object_wd(&p.fn_set_well_defined, &set)?, position)?
        );
        let formed = SourcePosition {
            before: 1,
            ..*position
        };
        let values = self.compile_function_packed_values(&signature, "_input")?;
        let params: Vec<_> = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect();
        let bindings: HashMap<_, _> = params
            .iter()
            .zip(&values)
            .map(|(p, v)| (p.id, v.clone()))
            .collect();
        let branches = p.statement.cases.iter().zip(&p.statement.equal_tos).map(|(guard, body)| {
            Ok(format!("(⟨(fun (_input : M.Value) => {}), (fun (_input : M.Value) => {})⟩ : Litex.FunctionBranch M)",
                self.compile_function_raw_predicate(&and_chain_as_fact(guard), &formed, &bindings)?,
                self.compile_function_raw_expression_bound(body, &formed, &bindings)?))
        }).collect::<Result<Vec<_>, LeanCompileError>>()?;
        let (base, base_set) = self.compile_function_semantic_base_domain(&signature, &formed)?;
        let target = self.compile_object_reference(&signature.ret_set, &formed)?;
        let guard = self.compile_function_packed_guard_template(&signature, &formed)?;
        let unpack = format!("obtain ⟨_members, _domain⟩ := (Litex.FunctionSignature.withGuard_domain {base} (Litex.denote {target}) {base_set} (Litex.isSet {target}) {guard} _input).mp _input_member");
        let members = if values.len() == 1 {
            "_members".into()
        } else {
            (0..values.len()).map(|i| format!("(by have _coordinate := Litex.FiniteFunction.coordinate_mem _members ({i} : Fin {}); norm_num [Litex.FiniteFunction.index] at _coordinate; exact _coordinate)",values.len())).collect::<Vec<_>>().join(" ")
        };
        let args = format!("{} {members} _domain", values.join(" "));
        let mut lines = vec![format!("let _signature := ({formed_set}).val")];
        for (i, branch) in branches.iter().enumerate() {
            lines.push(format!("let _branch_{i} := {branch}"));
        }
        let names = (0..count)
            .map(|i| format!("_branch_{i}"))
            .collect::<Vec<_>>();
        let list = format!("[{}]", names.join(", "));
        let covered = self
            .compile_piecewise_obligation(PiecewiseEvidence::Coverage(p, &p.coverage), &formed)
            .map_err(|mut e| {
                e.route = format!("PiecewiseFunction/Coverage/{}", e.route);
                e
            })?;
        lines.push(format!("have _coverage : {} := {}", covered.0, covered.1));
        let mut pair = 0;
        for i in 0..count {
            for j in i + 1..count {
                let proof = &p.disjoint[pair];
                pair += 1;
                if proof.i != i || proof.j != j {
                    return Err(LeanCompileError::unsupported("PiecewiseFunction/PairOrder"));
                }
                let checked = self
                    .compile_piecewise_obligation(PiecewiseEvidence::Disjoint(p, proof), &formed)
                    .map_err(|mut e| {
                        e.route = format!("PiecewiseFunction/Disjoint/{}", e.route);
                        e
                    })?;
                lines.push(format!(
                    "have _apart_{i}_{j} : {} := {}",
                    checked.0, checked.1
                ));
            }
        }
        for (i, proof) in p.case_return_checks.iter().enumerate() {
            if proof.case_index != i {
                return Err(LeanCompileError::unsupported(
                    "PiecewiseFunction/ReturnOrder",
                ));
            }
            let checked = self
                .compile_piecewise_obligation(PiecewiseEvidence::Return(p, proof), &formed)
                .map_err(|mut e| {
                    e.route = format!("PiecewiseFunction/Return/{}", e.route);
                    e
                })?;
            lines.push(format!("have _return_{i} : {} := {}", checked.0, checked.1));
        }
        lines.push(format!("apply Litex.piecewiseFn _signature {list}"));
        lines.push("refine ⟨?_, ?_, ?_⟩".into());
        let mut coverage = vec!["intro _input _input_member".into(), unpack.clone()];
        if count == 1 {
            coverage.push(format!(
                "exact ⟨_branch_0, {}, _coverage {args}⟩",
                list_member(0)
            ));
        } else {
            coverage.push(format!(
                "rcases _coverage {args} with {}",
                vec!["_case"; count].join(" | ")
            ));
            for i in 0..count {
                coverage.push(format!("· exact ⟨_branch_{i}, {}, _case⟩", list_member(i)));
            }
        }
        lines.push(format!("· {}", coverage.join("\n").replace('\n', "\n  ")));
        let mut apart = "List.Pairwise.nil".to_string();
        for i in (0..count).rev() {
            let proofs = (i+1..count).map(|j| format!("(by\n  intro _input _input_member\n  {unpack}\n  rintro ⟨_left, _right⟩\n  exact _apart_{i}_{j} {args} _left _right)")).collect::<Vec<_>>();
            apart = format!("(List.Pairwise.cons {} {apart})", list_elimination(&proofs));
        }
        lines.push(format!("· exact {apart}"));
        let returns = (0..count).map(|i| format!("(by\n  intro _input _input_member _case\n  {unpack}\n  exact _return_{i} {args} _case)")).collect::<Vec<_>>();
        lines.push(format!("· exact {}", list_elimination(&returns)));
        let value = format!(
            "(show Litex.Obj (M := M) (Litex.PiecewiseFn M) from by\n  {})",
            lines.join("\n").replace('\n', "\n  ")
        );
        let object = Obj::Identifier(IdentifierObj::from_bound_name(&p.statement.name));
        let mut declarations =
            vec![self.bind_alias(&p.statement.name, &object, &object, &value, false, position)?];
        let name = self.context_application(
            &format!("_object_i{}", p.statement.name.id.value()),
            position,
        );
        let stores = &p.store_and_infer_result;
        if stores.membership_fact_id != stores.membership.primary_fact_id()
            || stores.case_defining_fact_ids
                != stores
                    .case_defining
                    .iter()
                    .map(|s| s.primary_fact_id())
                    .collect::<Vec<_>>()
            || stores.case_defining.len() != count
            || stores.stored_fact_ids
                != std::iter::once(&stores.membership)
                    .chain(&stores.case_defining)
                    .flat_map(|s| s.stored_fact_ids())
                    .collect::<Vec<_>>()
        {
            return Err(LeanCompileError::unsupported(
                "PiecewiseFunction/StoreCapture",
            ));
        }
        let completed = SourcePosition {
            before: 6,
            ..*position
        };
        let membership = self.resolve_fact(stores.membership_fact_id, &completed)?;
        if !matches!(&membership, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element == object && f.set == set)
        {
            return Err(LeanCompileError::unsupported(
                "PiecewiseFunction/MembershipSubject",
            ));
        }
        self.validate_store(&stores.membership.store, &membership)?;
        let member = (
            format!("Litex.In {name} (Litex.fnSet ({name}).val.signature)"),
            format!("(Litex.piecewiseFnInFnSet {name})"),
        );
        declarations.push(self.emit_internal_fact(&membership, &member, &completed)?);
        for (i, store) in stores.case_defining.iter().enumerate() {
            declarations.push(self.compile_piecewise_equation(p, i, store, &name, position)?);
        }
        Ok(declarations.join("\n\n"))
    }

    fn compile_piecewise_disjoint_component(
        &self,
        other: &Fact,
        excluded: &Fact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use super::compile_by_stmt_result::compile_by_contra_stmt_result::validate_atomic_negation;
        use super::compile_by_stmt_result::compile_classified_negation::quantifier_free_terms;
        let terms = quantifier_free_terms(other)?;
        let [components] = terms.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "PiecewiseFunction/DisjointConjunction",
            ));
        };
        for (i, atom) in components.iter().enumerate() {
            let hypothesis = conjunction_projection("_other", i, components.len());
            if let Ok(negative) =
                validate_atomic_negation(&Fact::AtomicFact(atom.clone()), excluded)
            {
                return Ok(if negative {
                    format!("({hypothesis} _excluded)")
                } else {
                    format!("(_excluded {hypothesis})")
                });
            }
            if let Fact::AtomicFact(excluded) = excluded {
                if let (Ok((a, b, strict)), Ok((c, d, other_strict))) =
                    (source_order_oriented(atom), source_order_oriented(excluded))
                {
                    if a == d && b == c && strict != other_strict {
                        let a = self.compile_object_reference(a, position)?;
                        let b = self.compile_object_reference(b, position)?;
                        let rule = if strict { "ltLeTrans" } else { "leLtTrans" };
                        return Ok(format!("(Litex.ltNotSame {a} {a} (Litex.{rule} {a} {b} {a} {hypothesis} _excluded) (Litex.sameRefl {a}))"));
                    }
                }
            }
        }
        Err(LeanCompileError::unsupported(
            "PiecewiseFunction/RecordedNegationSubject",
        ))
    }

    fn compile_piecewise_equation(
        &self,
        p: &ExecHaveFnEqualCaseByCaseStmtSuccessResult,
        index: usize,
        store: &StoreFactAndInferResult,
        object: &str,
        parent: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let position = SourcePosition {
            before: 7 + index,
            ..*parent
        };
        let formed = SourcePosition {
            before: 1,
            ..*parent
        };
        let source = self.resolve_fact(store.primary_fact_id(), &position)?;
        self.validate_store(&store.store, &source)?;
        let Fact::ForallFact(fact) = &source else {
            return Err(LeanCompileError::unsupported(
                "PiecewiseFunction/EquationFamily",
            ));
        };
        let signature = piecewise_signature(p);
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| (p, g.param_type.as_ref())))
            .collect::<Vec<_>>();
        let actual = fact
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| (p, &g.param_type)))
            .collect::<Vec<_>>();
        if parameters.len() != actual.len()
            || parameters
                .iter()
                .zip(&actual)
                .any(|((p, c), (q, t))| p.id != q.id || !matches!(t, ParamType::Obj(d) if *c == d))
        {
            return Err(LeanCompileError::unsupported(
                "PiecewiseFunction/EquationParameters",
            ));
        }
        let mut expected_dom = signature
            .dom_facts
            .iter()
            .map(function_guard_fact)
            .collect::<Result<Vec<_>, _>>()?;
        expected_dom.push(and_chain_as_fact(&p.statement.cases[index]));
        if fact.dom_facts != expected_dom || fact.then_facts.len() != 1 {
            return Err(LeanCompileError::unsupported(
                "PiecewiseFunction/EquationPremises",
            ));
        }
        let conclusion: Fact = fact.then_facts[0].clone().into();
        let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = &conclusion else {
            return Err(LeanCompileError::unsupported(
                "PiecewiseFunction/EquationConclusion",
            ));
        };
        let Obj::FnObj(call) = &eq.left else {
            return Err(LeanCompileError::unsupported(
                "PiecewiseFunction/EquationCall",
            ));
        };
        if !matches!(call.head.as_ref(), FnObjHead::Identifier(IdentifierObj::Plain {id,..}) if *id == p.statement.name.id)
            || call.body.len() != 1
            || call.body[0].len() != parameters.len()
            || call.body[0].iter().zip(&parameters).any(|(a, (p, _))| {
                a.as_ref() != &Obj::Identifier(IdentifierObj::from_bound_name(p))
            })
            || eq.right != p.statement.equal_tos[index]
        {
            return Err(LeanCompileError::unsupported(
                "PiecewiseFunction/EquationBody",
            ));
        }
        let mut bindings =
            HashMap::from([(p.statement.name.id, format!("(Litex.denote {object})"))]);
        let mut binders = Vec::new();
        let mut intros = Vec::new();
        let mut objects = Vec::new();
        let mut requirements = Vec::new();
        for ((parameter, carrier), store) in parameters.iter().zip(
            &p.case_return_checks[index]
                .binder_introduction
                .defined_params
                .store_and_infer_results,
        ) {
            let id = parameter.id.value();
            let name = format!("_value_i{id}");
            let member = format!("h_{}", store.primary_fact_id().value());
            let raw = format!("(Litex.denote {name})");
            let carrier =
                self.compile_function_raw_expression_bound(carrier, &formed, &bindings)?;
            binders.push(format!("{{_Host_i{id} : Type v{id}}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({name} : Litex.Obj (M := M) _Host_i{id}) ({member} : M.mem {raw} {carrier})"));
            intros.extend([
                format!("_Host_i{id}"),
                format!("_rep_i{id}"),
                name.clone(),
                member.clone(),
            ]);
            bindings.insert(parameter.id, raw);
            objects.push(name);
            requirements.push(member);
        }
        for dom in &fact.dom_facts {
            let h = format!("h_{}", dom.fact_id().value());
            binders.push(format!(
                "({h} : {})",
                self.compile_function_raw_predicate(dom, &formed, &bindings)?
            ));
            intros.push(h.clone());
            requirements.push(h);
        }
        let case_guard = requirements.pop().unwrap();
        let (members, guard) = self.compile_function_domain_certificates(
            &signature,
            &objects,
            &requirements,
            &formed,
        )?;
        let values = objects
            .iter()
            .map(|o| format!("(Litex.denote {o})"))
            .collect::<Vec<_>>();
        let packed = if values.len() == 1 {
            values[0].clone()
        } else {
            format!(
                "(Litex.FiniteFunction.tupleValue (M := M) ![{}])",
                values.join(", ")
            )
        };
        let (base, base_set) = self.compile_function_semantic_base_domain(&signature, &formed)?;
        let target = self.compile_object_reference(&signature.ret_set, &formed)?;
        let packed_guard = self.compile_function_packed_guard_template(&signature, &formed)?;
        let member = if values.len() == 1 {
            members[0].clone()
        } else {
            let sets = if Self::function_uses_numeric_interface(&signature) {
                let mut d = self.compile_function_domains(&signature, &formed)?;
                d.pop();
                d.into_iter()
                    .map(|v| format!("M.standard {v}"))
                    .collect::<Vec<_>>()
            } else {
                self.compile_function_input_sets(&signature, &formed)?
                    .iter()
                    .map(|v| format!("Litex.denote {v}"))
                    .collect()
            };
            format!(
                "(Litex.FiniteFunction.tuple_inCart ![{}] ![{}] {})",
                values.join(", "),
                sets.join(", "),
                finite_vector_proof(&members)
            )
        };
        let guard_template = self.compile_function_guard_template(&signature, &formed)?;
        let guard_eq =
            self.compile_function_packed_application_equality(&guard_template, &values)?;
        let guard_proof = format!(
            "(Eq.mpr {guard_eq} ({guard} : {guard_template} {}))",
            values.join(" ")
        );
        let mut lines=vec![format!("intro {}",intros.join(" ")),format!("have _case_domain : M.mem {packed} ({object}).val.signature.domain := (Litex.FunctionSignature.withGuard_domain {base} (Litex.denote {target}) {base_set} (Litex.isSet {target}) {packed_guard} {packed}).mpr ⟨{member}, {guard_proof}⟩")];
        let raw = piecewise_raw_bindings(p);
        let raw_binders = parameters
            .iter()
            .map(|(p, _)| format!("(_raw_i{} : M.Value)", p.id.value()))
            .collect::<Vec<_>>()
            .join(" ");
        let case_template = format!(
            "(fun {raw_binders} => {})",
            self.compile_function_raw_predicate(
                &expected_dom[expected_dom.len() - 1],
                &formed,
                &raw
            )?
        );
        let body_template = format!(
            "(fun {raw_binders} => {})",
            self.compile_function_raw_expression_bound(&eq.right, &formed, &raw)?
        );
        let packed_values = self.compile_function_packed_values(&signature, "_input")?;
        let branch=format!("(⟨(fun (_input : M.Value) => {case_template} {}), (fun (_input : M.Value) => {body_template} {})⟩ : Litex.FunctionBranch M)",packed_values.join(" "),packed_values.join(" "));
        let case_eq = self.compile_function_packed_application_equality(&case_template, &values)?;
        let body_eq = self.compile_function_packed_application_equality(&body_template, &values)?;
        lines.push(format!("exact (Litex.piecewiseFn_call_eq {object} {branch} {} {packed} _case_domain (Eq.mpr {case_eq} ({case_guard} : {case_template} {}))).trans {body_eq}",list_member(index),values.join(" ")));
        let result = (
            format!(
                "∀ {}, {}",
                binders.join(" "),
                self.compile_function_raw_predicate(&conclusion, &position, &bindings)?
            ),
            format!("(by\n  {})", lines.join("\n").replace('\n', "\n  ")),
        );
        self.emit_internal_fact(&source, &result, &position)
    }

    fn compile_piecewise_obligation(
        &self,
        evidence: PiecewiseEvidence<'_>,
        parent: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let p = evidence.declaration();
        let signature = piecewise_signature(p);
        // Coverage already checked every guard's formation for these exact
        // source parameters. Reopen only that formation with explicit binder
        // aliases; branch hypotheses and truth never escape their own scope.
        let coverage = PiecewiseEvidence::Coverage(p, &p.coverage);
        let coverage_header = SourcePosition::new(
            Some(parent),
            SourceOwner::Piecewise(coverage),
            coverage.head_len(),
        );
        let VerifyFactResult::OrFact(coverage_result) = &p.coverage.coverage_check else {
            return Err(LeanCompileError::unsupported(
                "PiecewiseFunction/CoverageFamily",
            ));
        };
        let VerifyOrFactResult::Success(coverage_result) = coverage_result.as_ref() else {
            return Err(LeanCompileError::unsupported(
                "PiecewiseFunction/CoverageFailed",
            ));
        };
        let coverage_formation = SourcePosition::new(
            Some(&coverage_header),
            SourceOwner::Verify(&p.coverage.coverage_check),
            coverage_result.well_defined_proof.branches.len(),
        );
        let is_coverage = matches!(evidence, PiecewiseEvidence::Coverage(..));
        let scope = SourcePosition::new(
            Some(if is_coverage {
                parent
            } else {
                &coverage_formation
            }),
            SourceOwner::Piecewise(evidence),
            0,
        );
        let formed = SourcePosition {
            before: evidence.head_len(),
            ..scope
        };
        let mut lines = if is_coverage {
            self.compile_piecewise_head(evidence, &scope)?
        } else {
            let mut lines = self.compile_piecewise_head(coverage, &coverage_header)?;
            self.compile_or_wd(
                &coverage_result.fact,
                &coverage_result.well_defined_proof,
                &coverage_formation,
            )?;
            for (source, target) in coverage
                .introduction()
                .defined_params
                .store_and_infer_results
                .iter()
                .zip(
                    &evidence
                        .introduction()
                        .defined_params
                        .store_and_infer_results,
                )
            {
                lines.push(format!(
                    "have h_{} := h_{}",
                    target.primary_fact_id().value(),
                    source.primary_fact_id().value()
                ));
            }
            lines.extend(
                self.compile_piecewise_head(evidence, &scope)?
                    .into_iter()
                    .skip(1),
            );
            lines
        };
        let bindings = piecewise_raw_bindings(p);
        let raw = |fact: &Fact| self.compile_function_raw_predicate(fact, &formed, &bindings);
        let conclusion = match evidence {
            PiecewiseEvidence::Coverage(_, proof) => {
                let fact = source_subject(&proof.coverage_check)?;
                if !matches!(&fact,Fact::OrFact(f) if f.facts == p.statement.cases) {
                    return Err(LeanCompileError::unsupported(
                        "PiecewiseFunction/CoverageSubject",
                    ));
                }
                let checked = self.compile_verify(&proof.coverage_check, &formed)?;
                lines.push(format!("exact {}", checked.1));
                raw(&fact)?
            }
            PiecewiseEvidence::Return(_, proof) => {
                let guard = and_chain_as_fact(&p.statement.cases[proof.case_index]);
                lines.push(format!("intro h_{}", guard.fact_id().value()));
                lines.extend(self.compile_piecewise_assumption(
                    &guard,
                    &proof.assumption_stored,
                    &raw(&guard)?,
                    &formed,
                )?);
                let body_site = SourcePosition {
                    before: formed.before + 1,
                    ..scope
                };
                let body = &p.statement.equal_tos[proof.case_index];
                let object = self.compile_wd(
                    success_object_wd(&proof.body_well_defined, body)?,
                    &body_site,
                )?;
                let checked = self.compile_verify(
                    &proof.body_in_ret_set,
                    &SourcePosition {
                        before: body_site.before + 1,
                        ..scope
                    },
                )?;
                let fact = source_subject(&proof.body_in_ret_set)?;
                if !matches!(&fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element == *body && f.set == *signature.ret_set)
                {
                    return Err(LeanCompileError::unsupported(
                        "PiecewiseFunction/ReturnSubject",
                    ));
                }
                lines.extend([
                    format!("have _formed_body := {object}"),
                    format!("exact {}", checked.1),
                ]);
                format!("({}) → ({})", raw(&guard)?, raw(&fact)?)
            }
            PiecewiseEvidence::Disjoint(_, proof) => {
                let left = and_chain_as_fact(&p.statement.cases[proof.i]);
                let right = and_chain_as_fact(&p.statement.cases[proof.j]);
                let assumption = self.resolve_fact(
                    proof.assumption_stored.primary_fact_id(),
                    &SourcePosition {
                        before: formed.before + 1,
                        ..scope
                    },
                )?;
                let (other, reverse) = if assumption == left {
                    (&right, false)
                } else if assumption == right {
                    (&left, true)
                } else {
                    return Err(LeanCompileError::unsupported(
                        "PiecewiseFunction/DisjointAssumption",
                    ));
                };
                let id = assumption.fact_id().value();
                lines.push(if reverse {
                    format!("intro _other h_{id}")
                } else {
                    format!("intro h_{id} _other")
                });
                lines.extend(self.compile_piecewise_assumption(
                    &assumption,
                    &proof.assumption_stored,
                    &raw(&assumption)?,
                    &formed,
                )?);
                let site = SourcePosition {
                    before: formed.before + 1,
                    ..scope
                };
                let checked = self.compile_verify(&proof.negated_component, &site)?;
                lines.push(format!("have _excluded : {} := {}", checked.0, checked.1));
                lines.push(format!(
                    "exact {}",
                    self.compile_piecewise_disjoint_component(
                        other,
                        &source_subject(&proof.negated_component)?,
                        &SourcePosition {
                            before: site.before + 1,
                            ..site
                        }
                    )?
                ));
                format!("({}) → ({}) → False", raw(&left)?, raw(&right)?)
            }
        };
        Ok((
            self.compile_function_raw_quantified(&signature, &conclusion, parent)?,
            format!("(by\n  {})", lines.join("\n").replace('\n', "\n  ")),
        ))
    }

    fn compile_piecewise_head(
        &self,
        evidence: PiecewiseEvidence<'_>,
        scope: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let p = evidence.declaration();
        let signature = piecewise_signature(p);
        let introduction = evidence.introduction();
        self.validate_parameter_store_capture(&introduction.defined_params)?;
        let parameters: Vec<_> = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| (p, g.param_type.as_ref())))
            .collect();
        if parameters.len() != introduction.defined_params.store_and_infer_results.len()
            || signature.dom_facts.len() != introduction.assumed_dom_facts.len()
        {
            return Err(LeanCompileError::unsupported(
                "PiecewiseFunction/HeaderCapture",
            ));
        }
        let inputs: Vec<_> = introduction
            .defined_params
            .store_and_infer_results
            .iter()
            .map(|s| format!("h_{}", s.primary_fact_id().value()))
            .collect();
        let positive = self.compile_function_positive_inputs(&signature, scope)?;
        let guards: Vec<_> = positive
            .iter()
            .map(|id| format!("_positive_i{}", id.value()))
            .chain(
                introduction
                    .assumed_dom_facts
                    .iter()
                    .map(|s| format!("h_{}", s.primary_fact_id().value())),
            )
            .collect();
        let raw = parameters
            .iter()
            .map(|(p, _)| format!("_raw_i{}", p.id.value()))
            .collect::<Vec<_>>()
            .join(" ");
        let mut lines = vec![match guards.len() {
            0 => format!("intro {raw} {} _", inputs.join(" ")),
            1 => format!("intro {raw} {} {}", inputs.join(" "), guards[0]),
            _ => format!("rintro {raw} {} ⟨{}⟩", inputs.join(" "), guards.join(", ")),
        }];
        for (i, ((parameter, carrier), store)) in parameters
            .iter()
            .zip(&introduction.defined_params.store_and_infer_results)
            .enumerate()
        {
            let site = SourcePosition {
                before: i + 1,
                ..*scope
            };
            let fact = self.resolve_fact(store.primary_fact_id(), &site)?;
            let obj = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
            if !matches!(&fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element == obj && f.set == **carrier)
            {
                return Err(LeanCompileError::unsupported(
                    "PiecewiseFunction/ParameterSubject",
                ));
            }
            self.validate_store(&store.store, &fact)?;
            let id = parameter.id.value();
            let h = &inputs[i];
            lines.push(format!(
                "let _value_i{id} := Litex.semanticObject (M := M) _raw_i{id} (M.member_isSet {h})"
            ));
            let term = if positive.contains(&parameter.id) {
                format!(
                    "((Litex.positiveReal_members (M := M) _raw_i{id}).mpr ⟨{h}, _positive_i{id}⟩)"
                )
            } else {
                h.clone()
            };
            let member = (self.fact_proposition(&fact, &site)?, h.clone());
            lines.push(format!("have {h} : {} := {term}", member.0));
            lines.extend(self.compile_parameter_inferences(store, &fact, &member, &site)?);
        }
        for (i, (source, store)) in signature
            .dom_facts
            .iter()
            .zip(&introduction.assumed_dom_facts)
            .enumerate()
        {
            let fact = function_guard_fact(source)?;
            self.validate_store(&store.store, &fact)?;
            let site = SourcePosition {
                before: parameters.len() + i + 1,
                ..*scope
            };
            let h = format!("h_{}", fact.fact_id().value());
            let proposition = self.fact_proposition(&fact, &site)?;
            lines.push(format!("have {h} : {proposition} := {h}"));
            lines.extend(self.compile_stored_inferences(store, &fact, &(proposition, h), &site)?);
        }
        Ok(lines)
    }

    fn compile_piecewise_assumption(
        &self,
        fact: &Fact,
        store: &StoreFactAndInferResult,
        proposition: &str,
        prior: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        self.validate_store(&store.store, fact)?;
        let site = SourcePosition {
            before: prior.before + 1,
            ..*prior
        };
        let h = format!("h_{}", fact.fact_id().value());
        let proposition = proposition.to_string();
        let mut lines = vec![format!("have {h} : {proposition} := {h}")];
        lines.extend(self.compile_stored_inferences(store, fact, &(proposition, h), &site)?);
        Ok(lines)
    }
}

pub(super) fn piecewise_signature(p: &ExecHaveFnEqualCaseByCaseStmtSuccessResult) -> FnSet {
    FnSet {
        set_bound_parameters: p.statement.fn_set_clause.set_bound_parameters.clone(),
        dom_facts: p.statement.fn_set_clause.dom_facts.clone(),
        ret_set: Box::new(p.statement.fn_set_clause.ret_set.clone()),
    }
}

fn piecewise_raw_bindings(
    p: &ExecHaveFnEqualCaseByCaseStmtSuccessResult,
) -> HashMap<IdentifierId, String> {
    p.statement
        .fn_set_clause
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|g| &g.params)
        .map(|p| (p.id, format!("_raw_i{}", p.id.value())))
        .collect()
}

fn list_member(index: usize) -> String {
    let mut proof = "(List.mem_cons_self)".to_string();
    for _ in 0..index {
        proof = format!("(List.mem_cons_of_mem _ {proof})");
    }
    proof
}

fn list_elimination(proofs: &[String]) -> String {
    let mut lines = vec!["intro _branch _member".to_string()];
    for proof in proofs {
        lines.push("rcases List.mem_cons.mp _member with rfl | _member".into());
        lines.push(format!("· exact {proof}"));
    }
    lines.push("cases _member".into());
    format!("(by\n  {})", lines.join("\n").replace('\n', "\n  "))
}
