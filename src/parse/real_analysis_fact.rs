//! Parse the dedicated real-analysis properties without consulting execution state.
use crate::ast::line_file::SourceLine;
use crate::prelude::*;
use crate::runtime::RuntimeParseError;

pub(crate) fn real_analysis_fact_arity(name: &str) -> Option<usize> {
    match name {
        "is_real_upper_bound" | "is_real_lower_bound" => Some(2),
        "is_real_bounded_above" | "is_real_bounded_below" | "is_real_bounded" => Some(1),
        "is_seq_nondecreasing"
        | "is_seq_nonincreasing"
        | "is_seq_strictly_increasing"
        | "is_seq_strictly_decreasing"
        | "is_seq_bounded_above"
        | "is_seq_bounded_below"
        | "is_seq_bounded"
        | "is_seq_cauchy"
        | "is_seq_convergent" => Some(1),
        "is_real_accumulation_at" | "is_real_accumulation_left" | "is_real_accumulation_right" => {
            Some(2)
        }
        "is_continuous_at" | "is_continuous_left" | "is_continuous_right" => Some(2),
        "is_continuous" | "is_uniformly_continuous" => Some(1),
        "has_riemann_integral" => Some(4),
        "is_riemann_integrable" => Some(3),
        "has_derivative_at" => Some(3),
        "is_differentiable_at" => Some(2),
        "is_lipschitz" => Some(2),
        _ => None,
    }
}

impl Runtime {
    pub(crate) fn parse_real_analysis_fact(
        &mut self,
        name: &str,
        args: &[Obj],
        positive: bool,
        line_file: &SourceLine,
    ) -> RuntimeResult<Option<AtomicFact>> {
        let Some(arity) = real_analysis_fact_arity(name) else {
            return Ok(None);
        };
        if args.len() != arity {
            return Err(RuntimeParseError::new(
                format!("`{name}` requires {arity} arguments, got {}", args.len()),
                line_file.line,
                line_file.origin.clone(),
            )
            .into());
        }
        let fact_id = self.global_ids.allocate_fact_id();
        let line_file = Some(line_file.clone());
        let result = match name {
            "is_real_upper_bound" | "is_real_lower_bound" => {
                let direction = match name {
                    "is_real_upper_bound" => RealBoundDirection::Upper,
                    "is_real_lower_bound" => RealBoundDirection::Lower,
                    _ => unreachable!("matched property group"),
                };
                if positive {
                    RealSetBoundFact {
                        fact_id,
                        set: args[0].clone(),
                        bound: args[1].clone(),
                        direction,
                        line_file,
                    }
                    .into()
                } else {
                    NotRealSetBoundFact {
                        fact_id,
                        set: args[0].clone(),
                        bound: args[1].clone(),
                        direction,
                        line_file,
                    }
                    .into()
                }
            }
            "is_real_bounded_above" | "is_real_bounded_below" | "is_real_bounded" => {
                let boundedness = match name {
                    "is_real_bounded_above" => RealBoundedness::Above,
                    "is_real_bounded_below" => RealBoundedness::Below,
                    "is_real_bounded" => RealBoundedness::Both,
                    _ => unreachable!("matched property group"),
                };
                if positive {
                    RealSetBoundedFact {
                        fact_id,
                        set: args[0].clone(),
                        boundedness,
                        line_file,
                    }
                    .into()
                } else {
                    NotRealSetBoundedFact {
                        fact_id,
                        set: args[0].clone(),
                        boundedness,
                        line_file,
                    }
                    .into()
                }
            }
            "is_seq_nondecreasing"
            | "is_seq_nonincreasing"
            | "is_seq_strictly_increasing"
            | "is_seq_strictly_decreasing"
            | "is_seq_bounded_above"
            | "is_seq_bounded_below"
            | "is_seq_bounded"
            | "is_seq_cauchy"
            | "is_seq_convergent" => {
                let property = match name {
                    "is_seq_nondecreasing" => SequenceAnalysisProperty::Nondecreasing,
                    "is_seq_nonincreasing" => SequenceAnalysisProperty::Nonincreasing,
                    "is_seq_strictly_increasing" => SequenceAnalysisProperty::StrictlyIncreasing,
                    "is_seq_strictly_decreasing" => SequenceAnalysisProperty::StrictlyDecreasing,
                    "is_seq_bounded_above" => SequenceAnalysisProperty::BoundedAbove,
                    "is_seq_bounded_below" => SequenceAnalysisProperty::BoundedBelow,
                    "is_seq_bounded" => SequenceAnalysisProperty::Bounded,
                    "is_seq_cauchy" => SequenceAnalysisProperty::Cauchy,
                    "is_seq_convergent" => SequenceAnalysisProperty::Convergent,
                    _ => unreachable!("matched property group"),
                };
                if positive {
                    SequenceAnalysisFact {
                        fact_id,
                        sequence: args[0].clone(),
                        property,
                        line_file,
                    }
                    .into()
                } else {
                    NotSequenceAnalysisFact {
                        fact_id,
                        sequence: args[0].clone(),
                        property,
                        line_file,
                    }
                    .into()
                }
            }
            "is_real_accumulation_at"
            | "is_real_accumulation_left"
            | "is_real_accumulation_right" => {
                let side = match name {
                    "is_real_accumulation_at" => RealApproachSide::Both,
                    "is_real_accumulation_left" => RealApproachSide::Left,
                    "is_real_accumulation_right" => RealApproachSide::Right,
                    _ => unreachable!("matched property group"),
                };
                if positive {
                    RealAccumulationFact {
                        fact_id,
                        domain: args[0].clone(),
                        point: args[1].clone(),
                        side,
                        line_file,
                    }
                    .into()
                } else {
                    NotRealAccumulationFact {
                        fact_id,
                        domain: args[0].clone(),
                        point: args[1].clone(),
                        side,
                        line_file,
                    }
                    .into()
                }
            }
            "is_continuous_at" | "is_continuous_left" | "is_continuous_right" => {
                let side = match name {
                    "is_continuous_at" => RealApproachSide::Both,
                    "is_continuous_left" => RealApproachSide::Left,
                    "is_continuous_right" => RealApproachSide::Right,
                    _ => unreachable!("matched property group"),
                };
                if positive {
                    FunctionContinuousAtFact {
                        fact_id,
                        function: args[0].clone(),
                        point: args[1].clone(),
                        side,
                        line_file,
                    }
                    .into()
                } else {
                    NotFunctionContinuousAtFact {
                        fact_id,
                        function: args[0].clone(),
                        point: args[1].clone(),
                        side,
                        line_file,
                    }
                    .into()
                }
            }
            "is_continuous" | "is_uniformly_continuous" => {
                let property = match name {
                    "is_continuous" => FunctionContinuityProperty::Continuous,
                    "is_uniformly_continuous" => FunctionContinuityProperty::UniformContinuous,
                    _ => unreachable!("matched property group"),
                };
                if positive {
                    FunctionContinuousFact {
                        fact_id,
                        function: args[0].clone(),
                        property,
                        line_file,
                    }
                    .into()
                } else {
                    NotFunctionContinuousFact {
                        fact_id,
                        function: args[0].clone(),
                        property,
                        line_file,
                    }
                    .into()
                }
            }
            "has_riemann_integral" => {
                if positive {
                    HasRiemannIntegralFact {
                        fact_id,
                        function: args[0].clone(),
                        lower: args[1].clone(),
                        upper: args[2].clone(),
                        value: args[3].clone(),
                        line_file,
                    }
                    .into()
                } else {
                    NotHasRiemannIntegralFact {
                        fact_id,
                        function: args[0].clone(),
                        lower: args[1].clone(),
                        upper: args[2].clone(),
                        value: args[3].clone(),
                        line_file,
                    }
                    .into()
                }
            }
            "is_riemann_integrable" => {
                if positive {
                    FunctionRiemannIntegrableFact {
                        fact_id,
                        function: args[0].clone(),
                        lower: args[1].clone(),
                        upper: args[2].clone(),
                        line_file,
                    }
                    .into()
                } else {
                    NotFunctionRiemannIntegrableFact {
                        fact_id,
                        function: args[0].clone(),
                        lower: args[1].clone(),
                        upper: args[2].clone(),
                        line_file,
                    }
                    .into()
                }
            }
            "has_derivative_at" => {
                if positive {
                    HasDerivativeAtFact {
                        fact_id,
                        function: args[0].clone(),
                        point: args[1].clone(),
                        value: args[2].clone(),
                        line_file,
                    }
                    .into()
                } else {
                    NotHasDerivativeAtFact {
                        fact_id,
                        function: args[0].clone(),
                        point: args[1].clone(),
                        value: args[2].clone(),
                        line_file,
                    }
                    .into()
                }
            }
            "is_differentiable_at" => {
                if positive {
                    FunctionDifferentiableAtFact {
                        fact_id,
                        function: args[0].clone(),
                        point: args[1].clone(),
                        line_file,
                    }
                    .into()
                } else {
                    NotFunctionDifferentiableAtFact {
                        fact_id,
                        function: args[0].clone(),
                        point: args[1].clone(),
                        line_file,
                    }
                    .into()
                }
            }
            "is_lipschitz" => {
                if positive {
                    FunctionLipschitzFact {
                        fact_id,
                        function: args[0].clone(),
                        constant: args[1].clone(),
                        line_file,
                    }
                    .into()
                } else {
                    NotFunctionLipschitzFact {
                        fact_id,
                        function: args[0].clone(),
                        constant: args[1].clone(),
                        line_file,
                    }
                    .into()
                }
            }
            _ => unreachable!("real-analysis arity and parser agree"),
        };
        Ok(Some(result))
    }
}
