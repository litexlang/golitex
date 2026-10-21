use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::finite_function::FiniteFunctionSignatureProof;
use crate::execute::execute_fact_stmt::known_tuple::{literal_positive_usize, KnownTupleShapeProof};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::TupleCoordinateKnownProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_cart_inference_coordinate(
        &self,
        source: &InFact,
        index: usize,
        member: &str,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let Obj::ProductShape(ProductShape::Cart(cart)) = &source.set else {
            return Err(LeanCompileError::new(
                "CartInference/Carrier",
                "Coordinate inference needs its exact Cartesian membership seed.",
            ));
        };
        let factor = cart.args.get(index).ok_or_else(|| {
            LeanCompileError::new(
                "CartInference/Index",
                "The recorded coordinate index is outside the seed carrier.",
            )
        })?;
        let receiver = self.compile_object_reference(&source.element, position)?;
        self.compile_object_reference(&source.set, position)?;
        self.compile_object_reference(factor, position)?;
        let n = cart.args.len();
        let term = if let Obj::ProductShape(ProductShape::Tuple(tuple)) = &source.element {
            if tuple.args.len() != n {
                return Err(LeanCompileError::new(
                    "CartInference/TupleArity",
                    "A literal tuple must have the complete Cartesian domain.",
                ));
            }
            self.compile_object_reference(&tuple.args[index], position)?
        } else {
            format!("(Litex.cartCall {receiver} _ (Litex.number (M := M) ({} : ℂ)) {member} (by change M.mem (M.number ({} : ℂ)) (Litex.FiniteFunction.indexSet {n}); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) ({index} : Fin {n}))))", index + 1, index + 1)
        };
        let proof = if matches!(&source.element, Obj::ProductShape(ProductShape::Tuple(_))) {
            format!("(by simpa only [Litex.FiniteFunction.call_tuple] using (Litex.FiniteFunction.coordinate_mem {member} ({index} : Fin {n})))")
        } else {
            coordinate_membership(member, index, n)
        };
        Ok((term, proof))
    }

    /// Resolve a constructor created by this original coordinate projection.
    /// Only the exact visible inferred store authorizes this path.
    pub(in crate::compile_to_lean) fn compile_cart_inferred_subject(
        &self,
        object: &Obj,
        store: &StoreFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        self.compile_cart_inferred_subject_from(object, store, position, None)
    }

    fn compile_cart_inferred_subject_from(
        &self,
        object: &Obj,
        store: &StoreFactResult,
        position: &SourcePosition<'_>,
        source_membership: Option<&InFact>,
    ) -> Result<Option<String>, LeanCompileError> {
        let mut current = Some(position);
        while let Some(cursor) = current {
            let inference = match cursor.owner {
                SourceOwner::AtomicInference(
                    Fact::AtomicFact(AtomicFact::InFact(source)),
                    crate::store_fact_and_infer::InferAtomicFactResult::InFact(rules),
                ) => Some((source, rules)),
                SourceOwner::PropInference(captured) => match (&captured.store, &captured.infer) {
                    (
                        StoreFactResult::AtomicFact(seed),
                        Some(crate::store_fact_and_infer::InferResult::AtomicFact(
                            crate::store_fact_and_infer::InferAtomicFactResult::InFact(rules),
                        )),
                    ) => match &seed.fact {
                        AtomicFact::InFact(source) => Some((source, rules)),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            };
            if let Some((source, rules)) = inference {
                if source_membership.is_some_and(|expected| expected != source) {
                    current = cursor.parent;
                    continue;
                }
                for rule in rules {
                    let crate::store_fact_and_infer::InferInFactResult::CartCoordinates(
                        projections,
                    ) = rule
                    else {
                        continue;
                    };
                    for (index, projection) in projections.coordinates.iter().enumerate() {
                        if projection.membership.primary_fact_id() != store.primary_fact_id() {
                            continue;
                        }
                        let StoreFactResult::AtomicFact(stored) = store else {
                            continue;
                        };
                        let AtomicFact::InFact(derived) = &stored.fact else {
                            continue;
                        };
                        if derived.element.ir() != object.ir() {
                            continue;
                        }
                        let Obj::ProductShape(ProductShape::Cart(cart)) = &source.set else {
                            return Err(LeanCompileError::new(
                                "CartInference/Carrier",
                                "The original coordinate projection has another source carrier.",
                            ));
                        };
                        let expected = crate::execute::execute_fact_stmt::finite_function::finite_function_coordinate(
                            &source.element, index,
                        ).map_err(|error| LeanCompileError::new("CartInference/Coordinate", &error))?;
                        if projection.coordinate_index != index
                            || projections.coordinates.len() != cart.args.len()
                            || derived.element.ir() != expected.ir()
                            || cart
                                .args
                                .get(index)
                                .is_none_or(|factor| factor.ir() != derived.set.ir())
                        {
                            return Err(LeanCompileError::new(
                                "CartInference/Subject",
                                "The selected projection differs from its original receiver, index or factor.",
                            ));
                        }
                        self.validate_store(
                            &projection.membership.store,
                            &Fact::AtomicFact(stored.fact.clone()),
                        )?;
                        let name = format!(
                            "_object_h{}",
                            projection.membership.primary_fact_id().value()
                        );
                        return Ok(Some(if cursor.is_local() {
                            name
                        } else {
                            self.context_application(&name, cursor)
                        }));
                    }
                }
            }
            current = cursor.parent;
        }
        Ok(None)
    }

    pub(in crate::compile_to_lean) fn compile_tuple_coordinate_member(
        &self,
        goal: &InFact,
        proof: &TupleCoordinateKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FnObj(application) = &goal.element else {
            return Err(LeanCompileError::new(
                "TupleCoordinate/Application",
                "Coordinate membership must describe its original function application.",
            ));
        };
        let (receiver, argument) = finite_call_parts(application)?;
        if literal_positive_usize(argument) != Some(proof.index) || proof.index == 0 {
            return Err(LeanCompileError::new(
                "TupleCoordinate/Index",
                "The selected coordinate index differs from the source argument.",
            ));
        }
        let cart = proof
            .shape
            .cart()
            .ok_or_else(|| LeanCompileError::unsupported("TupleCoordinate/LiteralShape"))?;
        let source_set = cart.args.get(proof.index - 1).ok_or_else(|| {
            LeanCompileError::new(
                "TupleCoordinate/Bounds",
                "The coordinate is outside the complete recorded domain.",
            )
        })?;
        let (_, member) = self.compile_cart_shape_member(&receiver, &proof.shape, position)?;
        let source = self.compile_object_reference(source_set, position)?;
        let target = self.compile_object_reference(&goal.set, position)?;
        let call = self.compile_object_reference(&goal.element, position)?;
        let equality = self.compile_fn_return_set_match(
            source_set,
            &goal.set,
            &proof.carrier_equal,
            position,
        )?;
        self.compile_object_reference(&receiver, position)?;
        let coordinate = coordinate_membership(&member, proof.index - 1, cart.args.len());
        Ok(format!("(Litex.inOfSame {call} {call} {source} {target} (Litex.sameRefl {call}) {equality} {coordinate})"))
    }

    pub(in crate::compile_to_lean) fn compile_finite_fn_call(
        &self,
        application: &FnObj,
        proof: &FnObjObjWellDefinedProof,
        finite: &FiniteFunctionSignatureProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let Some(call) = position.bound_fn_call(application, proof) {
            return Ok(call);
        }
        let (receiver, argument) = finite_call_parts(application)?;
        validate_finite_signature(finite)?;
        if proof.child_obj_well_defined.len() != 2 || proof.requirement_fact_verified.len() != 1 {
            return Err(LeanCompileError::new(
                "FiniteCall/Stages",
                "A finite call needs its receiver WD, argument WD and exact-domain membership.",
            ));
        }
        ensure_object(&receiver, &proof.child_obj_well_defined[0])?;
        ensure_object(argument, &proof.child_obj_well_defined[1])?;
        let receiver_term = self.compile_wd(
            &proof.child_obj_well_defined[0],
            &SourcePosition {
                before: 0,
                ..*position
            },
        )?;
        let argument_term = self.compile_wd(
            &proof.child_obj_well_defined[1],
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;
        let requirement = &proof.requirement_fact_verified[0];
        let domain = &finite.signature.set_bound_parameters.groups[0].param_type;
        if !matches!(source_subject(requirement)?, Fact::AtomicFact(AtomicFact::InFact(f))
            if f.element.ir() == argument.ir() && f.set.ir() == domain.ir())
        {
            return Err(LeanCompileError::new(
                "FiniteCall/DomainSubject",
                "The finite-call requirement names another argument or complete domain.",
            ));
        }
        let member = self
            .compile_verify(
                requirement,
                &SourcePosition {
                    before: 2,
                    ..*position
                },
            )?
            .1;
        let formed = SourcePosition {
            before: 3,
            ..*position
        };
        let (cart, cart_member) =
            self.compile_cart_shape_member(&receiver, &finite.source, &formed)?;
        let n = finite.source.dimension();
        if matches!(&finite.source, KnownTupleShapeProof::CartesianMembership(source)
            if source.subject_equal.path.is_empty() && source.carrier_equal.path.is_empty())
        {
            // The original coordinate inference already emitted this exact
            // cartCall. Reuse it only after validating this occurrence's WD,
            // and only for the same original Cartesian membership producer.
            if literal_positive_usize(argument).is_some() {
                let KnownTupleShapeProof::CartesianMembership(source) = &finite.source else {
                    unreachable!()
                };
                let object = Obj::FnObj(application.clone());
                if let Some(Some(reference)) =
                    position.with_visible_inferred_subject(&object, &mut |store, producer| {
                        self.compile_cart_inferred_subject_from(
                            &object,
                            store,
                            producer,
                            Some(&source.membership),
                        )
                    })?
                {
                    return Ok(reference);
                }
            }
            // The original membership names this exact Cartesian wrapper;
            // Lean can infer it from that citation. Validation above still
            // checks its source constructor and complete finite signature.
            if matches!(&receiver, Obj::Identifier(_) | Obj::Literal(_))
                && matches!(argument, Obj::Identifier(_) | Obj::Literal(_))
            {
                return Ok(format!("(Litex.cartCall {receiver_term} _ {argument_term} {cart_member} (Litex.indexSetMemberOfClosedRange (n := {n}) {member}))"));
            }
            return Ok(format!("(let _receiver := {receiver_term};\nlet _argument := {argument_term};\nLitex.cartCall _receiver _ _argument {cart_member}\n  (Litex.indexSetMemberOfClosedRange (p := _argument) (n := {n}) {member}))"));
        }
        // These are data definitions, not hypotheses. Term-level lets retain
        // their defining values when a later proof projects a call's receiver.
        Ok(format!("(let _receiver := {receiver_term};\nlet _argument := {argument_term};\nlet _cart := {cart};\nLitex.cartCall _receiver _cart _argument {cart_member}\n  (Litex.indexSetMemberOfClosedRange (p := _argument) (n := {n}) {member}))"))
    }

    /// The recorded Cartesian membership is transported only along its own
    /// source equality paths. The returned term has the literal cart wrapper.
    pub(in crate::compile_to_lean) fn compile_cart_shape_member(
        &self,
        receiver: &Obj,
        shape: &KnownTupleShapeProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        if let KnownTupleShapeProof::TupleEquality(proof) = shape {
            let tuple_object = Obj::ProductShape(ProductShape::Tuple(proof.value.clone()));
            let tuple = self.compile_object_reference(&tuple_object, position)?;
            let subject = self.compile_object_reference(receiver, position)?;
            let same =
                self.compile_equality_path(receiver, &tuple_object, &proof.tuple_equal, position)?;
            let cart = format!("(Litex.tupleSingletonCart {tuple})");
            let member = format!("(by\n  let _tuple := {tuple}\n  let _receiver := {subject}\n  have _same : Litex.Same _receiver _tuple := {same}\n  exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))");
            return Ok((cart, member));
        }
        let (membership, factors, subject_path, carrier_path, citation) = match shape {
            KnownTupleShapeProof::CartesianMembership(proof) => {
                let (cited, citation) =
                    self.cited_fact_reference(proof.membership.fact_id, position)?;
                let expected = Fact::AtomicFact(AtomicFact::InFact(proof.membership.clone()));
                if cited != &expected
                    || self.resolve_fact(proof.membership.fact_id, position)? != expected
                {
                    return Err(LeanCompileError::new(
                        "FiniteFunction/MembershipCitation",
                        "The recorded Cartesian membership differs from its visible original producer.",
                    ));
                }
                (
                    &proof.membership,
                    &proof.cart,
                    &proof.subject_equal,
                    &proof.carrier_equal,
                    citation,
                )
            }
            KnownTupleShapeProof::FunctionCodomain(proof) => {
                // This membership is an internal goal, not a published fact.
                // Its original signature-use evidence proves the call's output.
                let member = self.compile_fn_return_codomain(
                    &proof.membership,
                    &proof.membership_proof,
                    position,
                )?;
                (
                    &proof.membership,
                    &proof.cart,
                    &proof.function_equal,
                    &proof.carrier_equal,
                    member,
                )
            }
            other => {
                let source = match other {
                    KnownTupleShapeProof::TupleEquality(_) => "TupleEquality",
                    KnownTupleShapeProof::CartesianCoordinate(_) => "CartesianCoordinate",
                    _ => unreachable!(),
                };
                return Err(LeanCompileError::new(
                    "FiniteFunction/ShapeEvidence",
                    &format!(
                    "The recorded {source} shape does not yet have a Cartesian membership compiler."
                ),
                ));
            }
        };
        let literal = Obj::ProductShape(ProductShape::Cart(factors.clone()));
        let cart = self.compile_object_reference(&literal, position)?;
        let subject = self.compile_object_reference(receiver, position)?;
        if subject_path.path.is_empty() && carrier_path.path.is_empty() {
            if receiver.ir() != membership.element.ir() || membership.set.ir() != literal.ir() {
                return Err(LeanCompileError::new(
                    "Equality/PathEndpoint",
                    "An empty Cartesian equality path changes its source endpoint.",
                ));
            }
            // Both endpoints were just compiled. Identity transport needs the
            // original citation, not four more reconstructions of those objects.
            let citation = if matches!(shape, KnownTupleShapeProof::FunctionCodomain(_)) {
                format!("(show Litex.In {subject} {cart} from {citation})")
            } else {
                citation
            };
            return Ok((cart, citation));
        }
        let original = self.compile_object_reference(&membership.element, position)?;
        let carrier = self.compile_object_reference(&membership.set, position)?;
        let subject_equal =
            self.compile_equality_path(receiver, &membership.element, subject_path, position)?;
        let carrier_equal =
            self.compile_equality_path(&membership.set, &literal, carrier_path, position)?;
        Ok((cart.clone(), format!("(Litex.inOfSame {original} {subject} {carrier} {cart} ({subject_equal}).symm {carrier_equal} {citation})")))
    }

    pub(in crate::compile_to_lean) fn compile_finite_numeric_output(
        &self,
        application: &FnObj,
        proof: &FnObjObjWellDefinedProof,
        finite: &FiniteFunctionSignatureProof,
        position: &SourcePosition<'_>,
    ) -> Result<(StandardSet, String), LeanCompileError> {
        // A membership-only caller must still replay the original call WD.
        self.compile_finite_fn_call(application, proof, finite, position)?;
        self.compile_finite_output_after_call(application, finite, position)
    }

    /// The caller has just compiled this same call's complete WD. Retain its
    /// output evidence without recursively compiling and discarding the call.
    pub(super) fn compile_finite_output_after_call(
        &self,
        application: &FnObj,
        finite: &FiniteFunctionSignatureProof,
        position: &SourcePosition<'_>,
    ) -> Result<(StandardSet, String), LeanCompileError> {
        let (receiver, argument) = finite_call_parts(application)?;
        let Some(index) = literal_positive_usize(argument) else {
            return Err(LeanCompileError::unsupported(
                "FiniteFunction/VariableNumericCoordinate",
            ));
        };
        let cart = finite.source.cart().ok_or_else(|| {
            LeanCompileError::unsupported("FiniteFunction/LiteralNumericCoordinate")
        })?;
        let carrier = cart.args.get(index - 1).ok_or_else(|| {
            LeanCompileError::new(
                "FiniteFunction/Coordinate",
                "The numeric coordinate lies outside the recorded complete domain.",
            )
        })?;
        let output = self.compile_numeric_carrier(carrier, position)?;
        let (_, member) = self.compile_cart_shape_member(&receiver, &finite.source, position)?;
        self.compile_object_reference(&receiver, position)?;
        self.compile_object_reference(carrier, position)?;
        Ok((
            output,
            coordinate_membership(&member, index - 1, cart.args.len()),
        ))
    }
}

/// The selected coordinate rule uses a Fin index; the source call uses a
/// one-based complex numeral. The Core bridge checks their exact equality.
pub(super) fn coordinate_membership(member: &str, index: usize, arity: usize) -> String {
    format!(
        "(Litex.FiniteFunction.coordinate_mem_number (M := M) {member} ({index} : Fin {arity}) ({} : ℂ) (by norm_num))",
        index + 1,
    )
}

pub(in crate::compile_to_lean) fn finite_call_parts(
    application: &FnObj,
) -> Result<(Obj, &Obj), LeanCompileError> {
    let arguments = application
        .body
        .last()
        .ok_or_else(|| LeanCompileError::unsupported("FiniteCall/EmptyApplication"))?;
    if arguments.len() != 1 {
        return Err(LeanCompileError::new(
            "FiniteCall/Arity",
            "A finite function consumes exactly one coordinate index.",
        ));
    }
    let receiver = if application.body.len() > 1 {
        let mut receiver = application.clone();
        receiver.body.pop();
        Obj::FnObj(receiver)
    } else {
        match application.head.as_ref() {
            FnObjHead::Object(object) => object.as_ref().clone(),
            FnObjHead::Identifier(identifier) => Obj::Identifier(identifier.clone()),
            FnObjHead::AnonymousFnLiteral(function) => {
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.as_ref().clone()))
            }
            FnObjHead::InstantiatedTemplateObj(instance) => {
                Obj::InstantiatedTemplateObj(instance.clone())
            }
            FnObjHead::FieldAccess(field) => {
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(field.clone()))
            }
        }
    };
    Ok((receiver, &arguments[0]))
}

pub(in crate::compile_to_lean) fn validate_finite_signature(
    finite: &FiniteFunctionSignatureProof,
) -> Result<(), LeanCompileError> {
    let signature = &finite.signature;
    let n = finite.source.dimension();
    if signature.set_bound_parameters.groups.len() != 1
        || signature.set_bound_parameters.groups[0].params.len() != 1
        || !signature.dom_facts.is_empty()
    {
        return Err(LeanCompileError::new(
            "FiniteFunction/Signature",
            "The recorded finite signature has another parameter or guard shape.",
        ));
    }
    let domain = &signature.set_bound_parameters.groups[0].param_type;
    if !matches!(domain.as_ref(), Obj::SetFormer(SetFormer::ClosedRange(range))
        if matches!(range.start.as_ref(), Obj::Literal(Literal::Number(number)) if number.normalized_value == "1")
        && matches!(range.end.as_ref(), Obj::Literal(Literal::Number(number)) if number.normalized_value == n.to_string()))
    {
        return Err(LeanCompileError::new(
            "FiniteFunction/CompleteDomain",
            "The source signature must retain the complete one-based domain of this shape.",
        ));
    }
    let factors = match &finite.source {
        KnownTupleShapeProof::TupleEquality(p) => p
            .value
            .args
            .iter()
            .map(|value| {
                Obj::SetFormer(SetFormer::ListSet(ListSet {
                    list: vec![value.clone()],
                }))
            })
            .collect::<Vec<_>>(),
        _ => finite
            .source
            .cart()
            .expect("Cartesian shape")
            .args
            .iter()
            .map(|factor| factor.as_ref().clone())
            .collect(),
    };
    let mut factors = factors.into_iter();
    let mut output = factors
        .next()
        .unwrap_or_else(|| Obj::SetFormer(SetFormer::ListSet(ListSet { list: vec![] })));
    for factor in factors {
        output = Obj::SetOperator(SetOperator::Union(Union {
            left: Box::new(output),
            right: Box::new(factor),
        }));
    }
    if output.ir() != signature.ret_set.ir() {
        return Err(LeanCompileError::new("FiniteFunction/ReturnDomain", "The finite signature must retain the ordered union of its recorded coordinate carriers."));
    }
    Ok(())
}
