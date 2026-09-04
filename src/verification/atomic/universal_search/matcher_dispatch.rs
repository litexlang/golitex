//! Atomic argument dispatch and primitive identifier/function/number matching.

use super::*;

impl ArgMatcher<'_> {
    pub(super) fn match_atomic_fact_args_in_active_binding_scope(
        &mut self,
        atomic_fact_in_known_forall: &AtomicFact,
        given_fact: &AtomicFact,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if let Some(match_result) =
            self.match_in_fact_standard_set_target(atomic_fact_in_known_forall, given_fact)?
        {
            return Ok(match_result);
        }

        let atomic_fact_args_in_known_forall = atomic_fact_in_known_forall.args_ref();
        let given_args = given_fact.args_ref();
        let forward = self
            .match_args_in_active_binding_scope(&atomic_fact_args_in_known_forall, &given_args)?;
        return Ok(forward);
    }

    pub(super) fn match_in_fact_standard_set_target(
        &mut self,
        atomic_fact_in_known_forall: &AtomicFact,
        given_fact: &AtomicFact,
    ) -> Result<Option<Option<HashMap<String, Obj>>>, RuntimeError> {
        let (AtomicFact::InFact(known_in), AtomicFact::InFact(given_in)) =
            (atomic_fact_in_known_forall, given_fact)
        else {
            return Ok(None);
        };
        let (Obj::StandardSet(known_set), Obj::StandardSet(given_set)) =
            (&known_in.set, &given_in.set)
        else {
            return Ok(None);
        };

        let Some(element_map) = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
            &known_in.element,
            &given_in.element,
        )?
        else {
            return Ok(Some(None));
        };

        // Narrow known membership implies broader target membership directly.
        // Broad known membership may match a narrow target only when the narrow
        // membership is already a known atomic fact, not merely builtin-provable.
        if known_set.is_subset_eq(given_set) {
            return Ok(Some(Some(element_map)));
        }
        if given_set.is_subset_eq(known_set) {
            let known_only_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(given_fact)?;
            if known_only_result.is_success() {
                return Ok(Some(Some(element_map)));
            }
        }

        Ok(Some(None))
    }

    pub(super) fn match_args_in_active_binding_scope(
        &mut self,
        fact_args_in_known_forall: &[&Obj],
        given_fact_args: &[&Obj],
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if fact_args_in_known_forall.len() != given_fact_args.len() {
            return Ok(None);
        }

        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (arg_in_atomic_fact_in_known_forall, arg_in_given) in
            fact_args_in_known_forall.iter().zip(given_fact_args.iter())
        {
            let sub_map = match self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                arg_in_atomic_fact_in_known_forall,
                arg_in_given,
            )? {
                Some(m) => m,
                None => return Ok(None),
            };
            if !self.merge_arg_match_map_into(&mut merged, sub_map) {
                return Ok(None);
            }
        }

        Ok(Some(merged))
    }

    // Return None if the given arg does not match the known arg.
    // Return Some(HashMap::new()) if the given arg matches the known arg.
    pub(super) fn match_arg_in_atomic_fact_in_known_forall_with_given_arg(
        &mut self,
        known_arg: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match known_arg {
            // Only exact bound symbols bind; plain identifiers are fixed names.
            Obj::Atom(AtomObj::Identifier(ref id_known)) => {
                if id_known.symbol.is_some()
                    && obj_equality_key(known_arg) == obj_equality_key(given_arg)
                {
                    return Ok(Some(HashMap::new()));
                }
                match given_arg {
                    Obj::Atom(AtomObj::Identifier(id_given)) if id_known.name == id_given.name => {}
                    Obj::Atom(AtomObj::IdentifierWithMod(id_given))
                        if self.is_current_parse_module(&id_given.mod_name)
                            && id_known.name == id_given.name => {}
                    _ => return Ok(None),
                }
                Ok(Some(HashMap::new()))
            }
            Obj::Atom(AtomObj::IdentifierWithMod(ref id_known)) => {
                if id_known.symbol.is_some()
                    && obj_equality_key(known_arg) == obj_equality_key(given_arg)
                {
                    return Ok(Some(HashMap::new()));
                }
                self.match_arg_when_left_is_identifier_with_mod(id_known, given_arg)
            }
            Obj::Atom(AtomObj::Bound(ref bound)) => {
                if !self
                    .active_bindings
                    .iter()
                    .any(|active_id| *active_id == bound.symbol.id())
                {
                    return if obj_equality_key(known_arg) == obj_equality_key(given_arg) {
                        Ok(Some(HashMap::new()))
                    } else {
                        Ok(None)
                    };
                }
                let mut map = HashMap::new();
                map.insert(arg_match_binding_key(&bound.symbol), given_arg.clone());
                Ok(Some(map))
            }
            Obj::FnObj(ref f) => self.match_arg_when_left_is_fn_obj(f, given_arg),
            Obj::Number(ref left) => self.match_arg_when_left_is_number(left, given_arg),
            Obj::ImaginaryUnit(_) => {
                if matches!(given_arg, Obj::ImaginaryUnit(_)) {
                    Ok(Some(HashMap::new()))
                } else {
                    Ok(None)
                }
            }
            Obj::EulerNumber(_) => {
                if matches!(given_arg, Obj::EulerNumber(_)) {
                    Ok(Some(HashMap::new()))
                } else {
                    Ok(None)
                }
            }
            Obj::Pi(_) => {
                if matches!(given_arg, Obj::Pi(_)) {
                    Ok(Some(HashMap::new()))
                } else {
                    Ok(None)
                }
            }
            Obj::Add(ref a) => self.match_arg_when_left_is_add(&a.left, &a.right, given_arg),
            Obj::MatrixAdd(ref a) => {
                self.match_arg_when_left_is_matrix_add(&a.left, &a.right, given_arg)
            }
            Obj::MatrixSub(ref a) => {
                self.match_arg_when_left_is_matrix_sub(&a.left, &a.right, given_arg)
            }
            Obj::MatrixMul(ref a) => {
                self.match_arg_when_left_is_matrix_mul(&a.left, &a.right, given_arg)
            }
            Obj::MatrixScalarMul(ref a) => {
                self.match_arg_when_left_is_matrix_scalar_mul(&a.scalar, &a.matrix, given_arg)
            }
            Obj::MatrixPow(ref a) => {
                self.match_arg_when_left_is_matrix_pow(&a.base, &a.exponent, given_arg)
            }
            Obj::Sub(ref a) => self.match_arg_when_left_is_sub(&a.left, &a.right, given_arg),
            Obj::Mul(ref a) => self.match_arg_when_left_is_mul(&a.left, &a.right, given_arg),
            Obj::Div(ref a) => self.match_arg_when_left_is_div(&a.left, &a.right, given_arg),
            Obj::Mod(ref a) => self.match_arg_when_left_is_mod(&a.left, &a.right, given_arg),
            Obj::Quot(ref a) => match given_arg {
                Obj::Quot(g) => {
                    self.match_arg_binary_then_merge(&a.left, &a.right, &g.left, &g.right)
                }
                _ => Ok(None),
            },
            Obj::Gcd(ref a) => match given_arg {
                Obj::Gcd(g) => {
                    self.match_arg_binary_then_merge(&a.left, &a.right, &g.left, &g.right)
                }
                _ => Ok(None),
            },
            Obj::Lcm(ref a) => match given_arg {
                Obj::Lcm(g) => {
                    self.match_arg_binary_then_merge(&a.left, &a.right, &g.left, &g.right)
                }
                _ => Ok(None),
            },
            Obj::Min(ref a) => match given_arg {
                Obj::Min(g) => {
                    self.match_arg_binary_then_merge(&a.left, &a.right, &g.left, &g.right)
                }
                _ => Ok(None),
            },
            Obj::Max(ref a) => match given_arg {
                Obj::Max(g) => {
                    self.match_arg_binary_then_merge(&a.left, &a.right, &g.left, &g.right)
                }
                _ => Ok(None),
            },
            Obj::Pow(ref a) => self.match_arg_when_left_is_pow(&a.base, &a.exponent, given_arg),
            Obj::Abs(ref a) => self.match_arg_when_left_is_abs(a.arg.as_ref(), given_arg),
            Obj::Floor(ref a) => match given_arg {
                Obj::Floor(g) => {
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(&a.arg, &g.arg)
                }
                _ => Ok(None),
            },
            Obj::Ceil(ref a) => match given_arg {
                Obj::Ceil(g) => {
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(&a.arg, &g.arg)
                }
                _ => Ok(None),
            },
            Obj::Sin(ref a) => match given_arg {
                Obj::Sin(g) => {
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(&a.arg, &g.arg)
                }
                _ => Ok(None),
            },
            Obj::Arcsin(ref a) => match given_arg {
                Obj::Arcsin(g) => {
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(&a.arg, &g.arg)
                }
                _ => Ok(None),
            },
            Obj::Cos(ref a) => match given_arg {
                Obj::Cos(g) => {
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(&a.arg, &g.arg)
                }
                _ => Ok(None),
            },
            Obj::Tan(ref a) => match given_arg {
                Obj::Tan(g) => {
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(&a.arg, &g.arg)
                }
                _ => Ok(None),
            },
            Obj::Cot(ref a) => match given_arg {
                Obj::Cot(g) => {
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(&a.arg, &g.arg)
                }
                _ => Ok(None),
            },
            Obj::RealPart(ref a) => match given_arg {
                Obj::RealPart(g) => {
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(&a.arg, &g.arg)
                }
                _ => Ok(None),
            },
            Obj::ImaginaryPart(ref a) => match given_arg {
                Obj::ImaginaryPart(g) => {
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(&a.arg, &g.arg)
                }
                _ => Ok(None),
            },
            Obj::ComplexAbs(ref a) => match given_arg {
                Obj::ComplexAbs(g) => {
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(&a.arg, &g.arg)
                }
                _ => Ok(None),
            },
            Obj::Sqrt(ref a) => self.match_arg_when_left_is_sqrt(a.arg.as_ref(), given_arg),
            Obj::Exp(ref a) => match given_arg {
                Obj::Exp(g) => {
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(&a.arg, &g.arg)
                }
                _ => Ok(None),
            },
            Obj::Ln(ref a) => match given_arg {
                Obj::Ln(g) => {
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(&a.arg, &g.arg)
                }
                _ => Ok(None),
            },
            Obj::Sign(ref a) => match given_arg {
                Obj::Sign(g) => {
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(&a.arg, &g.arg)
                }
                _ => Ok(None),
            },
            Obj::Factorial(ref a) => match given_arg {
                Obj::Factorial(g) => {
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(&a.arg, &g.arg)
                }
                _ => Ok(None),
            },
            Obj::Log(ref a) => self.match_arg_when_left_is_log(&a.base, &a.arg, given_arg),
            Obj::Union(ref a) => self.match_arg_when_left_is_union(&a.left, &a.right, given_arg),
            Obj::Intersect(ref a) => {
                self.match_arg_when_left_is_intersect(&a.left, &a.right, given_arg)
            }
            Obj::SetMinus(ref a) => {
                self.match_arg_when_left_is_set_minus(&a.left, &a.right, given_arg)
            }
            Obj::BigUnion(ref a) => self.match_arg_when_left_is_big_union(&a.left, given_arg),
            Obj::BigIntersect(ref a) => {
                self.match_arg_when_left_is_big_intersect(&a.left, given_arg)
            }
            Obj::IndexUnion(ref left) => {
                let Obj::IndexUnion(given) = given_arg else {
                    return Ok(None);
                };
                self.match_args_in_active_binding_scope(
                    &[
                        left.index_set.as_ref(),
                        left.ambient_set.as_ref(),
                        left.family_fn.as_ref(),
                    ],
                    &[
                        given.index_set.as_ref(),
                        given.ambient_set.as_ref(),
                        given.family_fn.as_ref(),
                    ],
                )
            }
            Obj::IndexIntersect(ref left) => {
                let Obj::IndexIntersect(given) = given_arg else {
                    return Ok(None);
                };
                self.match_args_in_active_binding_scope(
                    &[
                        left.index_set.as_ref(),
                        left.ambient_set.as_ref(),
                        left.family_fn.as_ref(),
                    ],
                    &[
                        given.index_set.as_ref(),
                        given.ambient_set.as_ref(),
                        given.family_fn.as_ref(),
                    ],
                )
            }
            Obj::GeneralCart(ref left) => self.match_arg_when_left_is_general_cart(left, given_arg),
            Obj::ListSet(ref left) => self.match_arg_when_left_is_list_set(&left.list, given_arg),
            Obj::SetBuilder(ref left) => self.match_arg_when_left_is_set_builder(left, given_arg),
            Obj::FnSet(ref left) => self.match_arg_when_left_is_fn_set_with_params(left, given_arg),
            Obj::AnonymousFn(ref left) => {
                self.match_arg_when_left_is_anonymous_fn_with_params(left, given_arg)
            }
            // Standard-set inclusion is semantic, not structural equality.
            // Generic arguments are invariant: `P(N)` cannot prove `P(N+)`.
            // Membership-target widening/narrowing belongs exclusively to
            // `match_in_fact_standard_set_target`, where its direction and
            // premises are checked explicitly.
            Obj::StandardSet(known_set) => match given_arg {
                Obj::StandardSet(given_set)
                    if std::mem::discriminant(known_set) == std::mem::discriminant(given_set) =>
                {
                    Ok(Some(HashMap::new()))
                }
                _ => Ok(None),
            },
            Obj::Cart(ref left) => self.match_arg_when_left_is_cart(&left.args, given_arg),
            Obj::CartDim(ref left) => {
                self.match_arg_when_left_is_cart_dim(left.set.as_ref(), given_arg)
            }
            Obj::Proj(ref left) => {
                self.match_arg_when_left_is_proj(left.set.as_ref(), left.dim.as_ref(), given_arg)
            }
            Obj::TupleDim(ref left) => {
                self.match_arg_when_left_is_dim(left.arg.as_ref(), given_arg)
            }
            Obj::Tuple(ref left) => self.match_arg_when_left_is_tuple(&left.args, given_arg),
            Obj::FiniteSeqListObj(ref left) => {
                self.match_arg_when_left_is_finite_seq_list(&left.objs, given_arg)
            }
            Obj::FiniteSetSize(ref left) => {
                self.match_arg_when_left_is_finite_set_size(left.set.as_ref(), given_arg)
            }
            Obj::FiniteSetMax(ref left) => {
                self.match_arg_when_left_is_finite_set_max(left.set.as_ref(), given_arg)
            }
            Obj::FiniteSetMin(ref left) => {
                self.match_arg_when_left_is_finite_set_min(left.set.as_ref(), given_arg)
            }
            Obj::FnRange(ref left) => {
                self.match_arg_when_left_is_fn_range(left.function.as_ref(), given_arg)
            }
            Obj::Replacement(ref left) => self.match_arg_when_left_is_replacement(left, given_arg),
            Obj::Sum(ref left) => self.match_arg_when_left_is_sum(
                left.start.as_ref(),
                left.end.as_ref(),
                left.func.as_ref(),
                given_arg,
            ),
            Obj::SumOfFiniteSet(ref left) => self.match_arg_when_left_is_finite_set_sum(
                left.set.as_ref(),
                left.func.as_ref(),
                given_arg,
            ),
            Obj::Product(ref left) => self.match_arg_when_left_is_product(
                left.start.as_ref(),
                left.end.as_ref(),
                left.func.as_ref(),
                given_arg,
            ),
            Obj::ProductOfFiniteSet(ref left) => self.match_arg_when_left_is_finite_set_product(
                left.set.as_ref(),
                left.func.as_ref(),
                given_arg,
            ),
            Obj::Reduce(ref left) => self.match_arg_when_left_is_reduce(left, given_arg),
            Obj::FiniteSetReduce(ref left) => {
                self.match_arg_when_left_is_finite_set_reduce(left, given_arg)
            }
            Obj::Range(ref left) => {
                self.match_arg_when_left_is_range(left.start.as_ref(), left.end.as_ref(), given_arg)
            }
            Obj::ClosedRange(ref left) => self.match_arg_when_left_is_closed_range(
                left.start.as_ref(),
                left.end.as_ref(),
                given_arg,
            ),
            Obj::IntervalObj(ref left) => self.match_arg_when_left_is_interval(left, given_arg),
            Obj::OneSideInfinityIntervalObj(ref left) => {
                self.match_arg_when_left_is_one_side_infinity_interval(left, given_arg)
            }
            Obj::FiniteSeqSet(ref left) => self.match_arg_when_left_is_finite_seq_set(
                left.set.as_ref(),
                left.n.as_ref(),
                given_arg,
            ),
            Obj::SeqSet(ref left) => {
                self.match_arg_when_left_is_seq_set(left.set.as_ref(), given_arg)
            }
            Obj::MatrixListObj(ref left) => {
                self.match_arg_when_left_is_matrix_list(&left.rows, given_arg)
            }
            Obj::MatrixSet(ref left) => self.match_arg_when_left_is_matrix_set(
                left.set.as_ref(),
                left.row_len.as_ref(),
                left.col_len.as_ref(),
                given_arg,
            ),
            Obj::PowerSet(ref left) => {
                self.match_arg_when_left_is_power_set(left.set.as_ref(), given_arg)
            }
            Obj::ObjAtIndex(ref left) => self.match_arg_when_left_is_obj_at_index(
                left.obj.as_ref(),
                left.index.as_ref(),
                given_arg,
            ),
            Obj::StructObj(known) => match given_arg {
                Obj::StructObj(given) => {
                    if known.name.to_string() != given.name.to_string() {
                        return Ok(None);
                    }
                    self.match_arg_vec_then_merge(&known.params, &given.params)
                }
                _ => Ok(None),
            },
            Obj::ObjAsStructInstanceWithFieldAccess(known) => match given_arg {
                Obj::ObjAsStructInstanceWithFieldAccess(given) => {
                    if known.field_name != given.field_name {
                        return Ok(None);
                    }
                    self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        known.obj.as_ref(),
                        given.obj.as_ref(),
                    )
                }
                _ => Ok(None),
            },
            Obj::InstantiatedTemplateObj(known) => match given_arg {
                Obj::InstantiatedTemplateObj(given) => {
                    if known.template_name != given.template_name {
                        return Ok(None);
                    }
                    self.match_arg_vec_then_merge(&known.args, &given.args)
                }
                _ => Ok(None),
            },
        }
    }

    pub(super) fn arg_match_binding_is_active(&self, symbol: &SymbolRef) -> bool {
        self.active_bindings.contains(&symbol.id())
    }

    pub(super) fn match_arg_when_left_is_identifier_with_mod(
        &mut self,
        id_known: &IdentifierWithMod,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Atom(AtomObj::IdentifierWithMod(id_given)) => {
                if id_known.mod_name == id_given.mod_name && id_known.name == id_given.name {
                    Ok(Some(HashMap::new()))
                } else {
                    Ok(None)
                }
            }
            Obj::Atom(AtomObj::Identifier(id_given))
                if self.is_current_parse_module(&id_known.mod_name)
                    && id_known.name == id_given.name =>
            {
                Ok(Some(HashMap::new()))
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_fn_obj(
        &mut self,
        left: &FnObj,
        right: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match right {
            Obj::FnObj(ref right_fn) => {
                // body lengths must match
                if left.body.len() != right_fn.body.len() {
                    return Ok(None);
                }

                let left_head: Obj = left.head.as_ref().clone().into();
                let right_head: Obj = right_fn.head.as_ref().clone().into();

                // heads must match
                let head_match = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    &left_head,
                    &right_head,
                )?;
                let mut head_map = match head_match {
                    Some(m) => m,
                    None => return Ok(None),
                };

                for (left_row, right_row) in left.body.iter().zip(right_fn.body.iter()) {
                    if left_row.len() != right_row.len() {
                        return Ok(None);
                    }
                    for (left_arg, right_arg) in left_row.iter().zip(right_row.iter()) {
                        let sub_map = match self
                            .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                                left_arg.as_ref(),
                                right_arg.as_ref(),
                            )? {
                            Some(m) => m,
                            None => return Ok(None),
                        };
                        if !self.merge_arg_match_map_into(&mut head_map, sub_map) {
                            return Ok(None);
                        }
                    }
                }

                Ok(Some(head_map))
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_number(
        &mut self,
        left: &Number,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if !given_arg.evaluate_to_normalized_decimal_number().is_some() {
            return Ok(None);
        }
        let left_obj: Obj = left.clone().into();
        if left_obj.two_objs_can_be_calculated_and_equal_by_calculation(given_arg) {
            Ok(Some(HashMap::new()))
        } else {
            Ok(None)
        }
    }
}
