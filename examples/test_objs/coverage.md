# Obj coverage

Task: add detailed regression files for every current Litex Obj variant.

The inventory maps 99 terminal Obj paths to 99 dedicated positive files, with 594 positive cases, 289 rejection fixtures and 22 recorded gaps.

The earlier 2026-10-03 [audit](audit_2026-10-03.md) observed 67 direct
rejections. The subsequent [F authoring repairs](experience/problem_notes/f_authoring_repairs_2026-10-03.md)
promote 23 checked proof migrations and four unchanged recovered addition folds;
the recovered subtraction rejection stays in the negative corpus. Original gap
sources and receipts are archived in the authoring journal before retirement.
That F follow-up changed proofs and fixtures. The subsequent [exact numeric, periodic trig and modulus repair](experience/problem_notes/exact_numeric_periodic_modulus_2026-10-03.md) adds local Rust leaves, closes 14 gaps and adds 21 positive and five negative cases. Current versus retained-release receipts are distinguished in the journal.

The [remaining elementary follow-up](experience/problem_notes/remaining_elementary_gaps_2026-10-03.md) closes the other eight requested extrema, inverse and log goals. The focused current-source report covers all 13 involved object families; unrelated gaps remain in the manifest.

These counts describe coverage of written cases, not proof that the implementation is bug-free. The runner audits the enum tree and all `.lit` fixtures on every run.

| AST path | Positive file | Positive cases | Rejection fixtures | Recorded gaps |
| --- | --- | ---: | ---: | ---: |
| `Obj::Identifier::Plain` | [identifier_plain](identifier_plain.lit) | 6 | 3 | 0 |
| `Obj::FnObj` | [fn_obj](fn_obj.lit) | 9 | 5 | 0 |
| `Obj::Literal::Number` | [number](number.lit) | 9 | 3 | 0 |
| `Obj::Literal::ImaginaryUnit` | [imaginary_unit](imaginary_unit.lit) | 8 | 3 | 0 |
| `Obj::Literal::EulerNumber` | [euler_number](euler_number.lit) | 5 | 2 | 0 |
| `Obj::Literal::Pi` | [pi](pi.lit) | 5 | 2 | 0 |
| `Obj::ArithmeticOperator::Add` | [add](add.lit) | 7 | 2 | 0 |
| `Obj::ArithmeticOperator::Sub` | [sub](sub.lit) | 7 | 2 | 0 |
| `Obj::ArithmeticOperator::Neg` | [neg](neg.lit) | 6 | 2 | 0 |
| `Obj::ArithmeticOperator::Mul` | [mul](mul.lit) | 7 | 2 | 0 |
| `Obj::ArithmeticOperator::Div` | [div](div.lit) | 10 | 8 | 0 |
| `Obj::ArithmeticOperator::Pow` | [pow](pow.lit) | 12 | 3 | 0 |
| `Obj::ArithmeticOperator::Abs` | [abs](abs.lit) | 6 | 2 | 0 |
| `Obj::ArithmeticOperator::Min` | [min](min.lit) | 6 | 2 | 0 |
| `Obj::ArithmeticOperator::Max` | [max](max.lit) | 6 | 2 | 0 |
| `Obj::ArithmeticOperator::Floor` | [floor](floor.lit) | 6 | 2 | 0 |
| `Obj::ArithmeticOperator::Ceil` | [ceil](ceil.lit) | 6 | 2 | 0 |
| `Obj::ArithmeticOperator::Sign` | [sign](sign.lit) | 5 | 2 | 0 |
| `Obj::IntegerOperator::Mod` | [mod](mod.lit) | 7 | 3 | 0 |
| `Obj::IntegerOperator::Quot` | [quot](quot.lit) | 7 | 5 | 0 |
| `Obj::IntegerOperator::Gcd` | [gcd](gcd.lit) | 6 | 3 | 0 |
| `Obj::IntegerOperator::Lcm` | [lcm](lcm.lit) | 6 | 2 | 0 |
| `Obj::IntegerOperator::Factorial` | [factorial](factorial.lit) | 6 | 3 | 0 |
| `Obj::TrigOperator::Sin` | [sin](sin.lit) | 8 | 3 | 0 |
| `Obj::TrigOperator::Cos` | [cos](cos.lit) | 8 | 2 | 0 |
| `Obj::TrigOperator::Tan` | [tan](tan.lit) | 8 | 4 | 0 |
| `Obj::TrigOperator::Cot` | [cot](cot.lit) | 6 | 3 | 0 |
| `Obj::TrigOperator::Arcsin` | [arcsin](arcsin.lit) | 4 | 4 | 0 |
| `Obj::TrigOperator::Arccos` | [arccos](arccos.lit) | 4 | 4 | 0 |
| `Obj::TrigOperator::Arctan` | [arctan](arctan.lit) | 4 | 2 | 0 |
| `Obj::TrigOperator::Arccot` | [arccot](arccot.lit) | 4 | 2 | 0 |
| `Obj::ExpLogOperator::Exp` | [exp](exp.lit) | 6 | 2 | 0 |
| `Obj::ExpLogOperator::Ln` | [ln](ln.lit) | 5 | 4 | 0 |
| `Obj::ExpLogOperator::Log` | [log](log.lit) | 6 | 5 | 0 |
| `Obj::ExpLogOperator::Sqrt` | [sqrt](sqrt.lit) | 7 | 3 | 0 |
| `Obj::ComplexOperator::RealPart` | [real_part](real_part.lit) | 6 | 2 | 0 |
| `Obj::ComplexOperator::ImaginaryPart` | [imaginary_part](imaginary_part.lit) | 6 | 2 | 0 |
| `Obj::ComplexOperator::ComplexAbs` | [complex_abs](complex_abs.lit) | 15 | 4 | 0 |
| `Obj::SetOperator::Union` | [union](union.lit) | 6 | 2 | 0 |
| `Obj::SetOperator::Intersect` | [intersect](intersect.lit) | 6 | 2 | 0 |
| `Obj::SetOperator::SetMinus` | [set_minus](set_minus.lit) | 6 | 2 | 0 |
| `Obj::SetOperator::FamilyUnion` | [family_union](family_union.lit) | 2 | 2 | 3 |
| `Obj::SetOperator::FamilyIntersect` | [family_intersect](family_intersect.lit) | 3 | 2 | 4 |
| `Obj::SetOperator::PowerSet` | [power_set](power_set.lit) | 5 | 2 | 1 |
| `Obj::SetOperator::IndexUnion` | [index_union](index_union.lit) | 4 | 4 | 1 |
| `Obj::SetOperator::IndexIntersect` | [index_intersect](index_intersect.lit) | 4 | 4 | 1 |
| `Obj::SetOperator::IndexCart` | [index_cart](index_cart.lit) | 4 | 3 | 0 |
| `Obj::SetFormer::ListSet` | [list_set](list_set.lit) | 8 | 3 | 0 |
| `Obj::SetFormer::SetBuilder` | [set_builder](set_builder.lit) | 6 | 3 | 0 |
| `Obj::SetFormer::Range` | [range](range.lit) | 5 | 2 | 2 |
| `Obj::SetFormer::ClosedRange` | [closed_range](closed_range.lit) | 6 | 2 | 1 |
| `Obj::SetFormer::FiniteSeqSet` | [finite_seq_set](finite_seq_set.lit) | 4 | 3 | 1 |
| `Obj::SetFormer::SeqSet` | [seq_set](seq_set.lit) | 3 | 2 | 2 |
| `Obj::ProductShape::Cart` | [cart](cart.lit) | 5 | 3 | 1 |
| `Obj::ProductShape::Tuple` | [tuple](tuple.lit) | 6 | 2 | 0 |
| `Obj::ProductShape::CartDim` | [cart_dim](cart_dim.lit) | 4 | 2 | 0 |
| `Obj::ProductShape::TupleDim` | [tuple_dim](tuple_dim.lit) | 4 | 2 | 0 |
| `Obj::ProductShape::Proj` | [proj](proj.lit) | 4 | 4 | 0 |
| `Obj::ProductShape::ObjAtIndex` | [obj_at_index](obj_at_index.lit) | 6 | 5 | 0 |
| `Obj::FunctionSpace::FnSet` | [fn_set](fn_set.lit) | 6 | 3 | 0 |
| `Obj::FunctionSpace::AnonymousFn` | [anonymous_fn](anonymous_fn.lit) | 7 | 4 | 0 |
| `Obj::FunctionSpace::FnRange` | [fn_range](fn_range.lit) | 4 | 2 | 0 |
| `Obj::IteratedOperator::Sum` | [sum](sum.lit) | 16 | 12 | 0 |
| `Obj::IteratedOperator::Product` | [product](product.lit) | 11 | 6 | 0 |
| `Obj::IteratedOperator::SumOfFiniteSet` | [sum_of_finite_set](sum_of_finite_set.lit) | 13 | 8 | 0 |
| `Obj::IteratedOperator::ProductOfFiniteSet` | [product_of_finite_set](product_of_finite_set.lit) | 12 | 7 | 0 |
| `Obj::IteratedOperator::Reduce` | [reduce](reduce.lit) | 5 | 3 | 0 |
| `Obj::IteratedOperator::FiniteSetReduce` | [finite_set_reduce](finite_set_reduce.lit) | 6 | 3 | 0 |
| `Obj::FiniteSetStat::FiniteSetSize` | [finite_set_size](finite_set_size.lit) | 6 | 3 | 1 |
| `Obj::FiniteSetStat::FiniteSetMax` | [finite_set_max](finite_set_max.lit) | 6 | 5 | 0 |
| `Obj::FiniteSetStat::FiniteSetMin` | [finite_set_min](finite_set_min.lit) | 6 | 5 | 0 |
| `Obj::StructAndFieldAccessObj::StructObj` | [struct_obj](struct_obj.lit) | 4 | 3 | 0 |
| `Obj::StructAndFieldAccessObj::FieldAccess` | [field_access](field_access.lit) | 4 | 4 | 0 |
| `Obj::InstantiatedTemplateObj` | [instantiated_template_obj](instantiated_template_obj.lit) | 4 | 3 | 0 |
| `Obj::StandardSet::N` | [standard_set_n](standard_set_n.lit) | 5 | 2 | 0 |
| `Obj::StandardSet::NPos` | [standard_set_n_pos](standard_set_n_pos.lit) | 5 | 2 | 0 |
| `Obj::StandardSet::Z` | [standard_set_z](standard_set_z.lit) | 5 | 2 | 0 |
| `Obj::StandardSet::Q` | [standard_set_q](standard_set_q.lit) | 5 | 2 | 0 |
| `Obj::StandardSet::R` | [standard_set_r](standard_set_r.lit) | 5 | 2 | 0 |
| `Obj::StandardSet::C` | [standard_set_c](standard_set_c.lit) | 4 | 1 | 0 |
| `Obj::StandardSet::QPos` | [standard_set_q_pos](standard_set_q_pos.lit) | 5 | 2 | 0 |
| `Obj::StandardSet::RPos` | [standard_set_r_pos](standard_set_r_pos.lit) | 5 | 2 | 0 |
| `Obj::StandardSet::QNeg` | [standard_set_q_neg](standard_set_q_neg.lit) | 5 | 2 | 0 |
| `Obj::StandardSet::ZNeg` | [standard_set_z_neg](standard_set_z_neg.lit) | 5 | 2 | 0 |
| `Obj::StandardSet::RNeg` | [standard_set_r_neg](standard_set_r_neg.lit) | 5 | 2 | 0 |
| `Obj::StandardSet::QStar` | [standard_set_q_star](standard_set_q_star.lit) | 5 | 2 | 0 |
| `Obj::StandardSet::ZStar` | [standard_set_z_star](standard_set_z_star.lit) | 5 | 2 | 0 |
| `Obj::StandardSet::RStar` | [standard_set_r_star](standard_set_r_star.lit) | 5 | 2 | 0 |
| `Obj::StandardSet::CStar` | [standard_set_c_star](standard_set_c_star.lit) | 5 | 2 | 0 |
| `Obj::SetFormer::OneSideInfinityIntervalObj::LowerOpen` | [one_side_interval_lower_open](one_side_interval_lower_open.lit) | 4 | 2 | 0 |
| `Obj::SetFormer::OneSideInfinityIntervalObj::LowerClosed` | [one_side_interval_lower_closed](one_side_interval_lower_closed.lit) | 4 | 2 | 0 |
| `Obj::SetFormer::OneSideInfinityIntervalObj::UpperOpen` | [one_side_interval_upper_open](one_side_interval_upper_open.lit) | 4 | 2 | 0 |
| `Obj::SetFormer::OneSideInfinityIntervalObj::UpperClosed` | [one_side_interval_upper_closed](one_side_interval_upper_closed.lit) | 4 | 2 | 0 |
| `Obj::SetFormer::IntervalObj::LeftOpenRightOpen` | [interval_open_open](interval_open_open.lit) | 7 | 2 | 0 |
| `Obj::SetFormer::IntervalObj::LeftOpenRightClosed` | [interval_open_closed](interval_open_closed.lit) | 7 | 2 | 0 |
| `Obj::SetFormer::IntervalObj::LeftClosedRightOpen` | [interval_closed_open](interval_closed_open.lit) | 7 | 2 | 0 |
| `Obj::SetFormer::IntervalObj::LeftClosedRightClosed` | [interval_closed_closed](interval_closed_closed.lit) | 7 | 2 | 0 |
| `Obj::Identifier::WithExportFileId` | [identifier_with_export_file_id](identifier_with_export_file_id/main.lit) | 5 | 3 | 2 |
| `Obj::Identifier::WithModAndExportFileId` | [identifier_with_mod_and_export_file_id](identifier_with_mod_and_export_file_id/main.lit) | 5 | 3 | 2 |

## Helper variants

- `FnObjHead::Identifier` is exercised in [fn_obj.lit](fn_obj.lit).
- `FnObjHead::AnonymousFnLiteral` is exercised in [fn_obj.lit](fn_obj.lit).
- `FnObjHead::FieldAccess` is exercised in [fn_obj.lit](fn_obj.lit).
- `FnObjHead::InstantiatedTemplateObj` is exercised in [fn_obj.lit](fn_obj.lit).
- `FnSetSpace::Set` is exercised in [fn_set.lit](fn_set.lit).
- `FnSetSpace::Anon` is exercised in [anonymous_fn.lit](anonymous_fn.lit).

## Focus

Numeric operators test exact values and their defined carriers; parser precedence is covered by subtraction, division, power and factorial cases. Number sets and interval variants each have their own positive membership and exclusion boundaries. Functions test all head kinds, arity, refinement, codomain and closure use. Product/index cases test dimensions, nesting and forbidden indices. Set operators test emptiness where permitted, elementary laws, displayed sets and indexed families. The two qualified-identifier projects use different values with identical terminal names.

A missing direct proof, incomplete WD rule and incorrectly admitted object are different outcomes; consult [todo.md](todo.md) for concrete evidence. The initial corpus task changed no core source. The approved follow-up repaired numeric and aggregate owners without changing Obj/Stmt/Fact AST shapes; the current acceptance record separates that work from concurrent recoveries.
