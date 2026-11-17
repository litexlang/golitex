//! Explicit laws for finite-valued improper integrals.
use crate::builtin_theorem::ImproperIntegralTheorem;
use crate::execute::execute_fact_stmt::improper_integral::integral_region;
use crate::execute::execute_fact_stmt::real_analysis::analysis_apply;
use crate::execute::execute_fact_stmt::riemann_integral::helper::*;
use crate::prelude::*;

const NAMES: [[&str; 8]; 5] = [
    [
        "integral_open_closed_from_definition",
        "integral_open_closed_to_definition",
        "integral_open_closed_selected",
        "integral_open_closed_unique",
        "integral_open_closed_add",
        "integral_open_closed_scale",
        "integral_open_closed_congr",
        "integral_open_closed_reverse",
    ],
    [
        "integral_closed_open_from_definition",
        "integral_closed_open_to_definition",
        "integral_closed_open_selected",
        "integral_closed_open_unique",
        "integral_closed_open_add",
        "integral_closed_open_scale",
        "integral_closed_open_congr",
        "integral_closed_open_reverse",
    ],
    [
        "integral_open_from_definition",
        "integral_open_to_definition",
        "integral_open_selected",
        "integral_open_unique",
        "integral_open_add",
        "integral_open_scale",
        "integral_open_congr",
        "integral_open_reverse",
    ],
    [
        "integral_pos_inf_from_definition",
        "integral_pos_inf_to_definition",
        "integral_pos_inf_selected",
        "integral_pos_inf_unique",
        "integral_pos_inf_add",
        "integral_pos_inf_scale",
        "integral_pos_inf_congr",
        "",
    ],
    [
        "integral_neg_inf_from_definition",
        "integral_neg_inf_to_definition",
        "integral_neg_inf_selected",
        "integral_neg_inf_unique",
        "integral_neg_inf_add",
        "integral_neg_inf_scale",
        "integral_neg_inf_congr",
        "",
    ],
];

impl ImproperIntegralTheorem {
    pub fn from_name(name: &str) -> Option<Self> {
        if name.is_empty() {
            return None;
        }
        for (kind, row) in NAMES.iter().enumerate() {
            if let Some(rule) = row.iter().position(|candidate| *candidate == name) {
                return Some(Self { kind, rule });
            }
        }
        None
    }

    pub const fn name(self) -> &'static str {
        NAMES[self.kind][self.rule]
    }

    pub const fn arity(self) -> usize {
        let endpoints = if self.kind < 3 { 2 } else { 1 };
        endpoints
            + match self.rule {
                2 => 1,
                3 | 6 => 3,
                5 => 4,
                4 => 5,
                _ => 2,
            }
    }

    fn bounds(self, endpoints: &[Obj]) -> ImproperIntegralBounds {
        use ImproperIntegralBounds::*;
        let start = Box::new(endpoints[0].clone());
        match self.kind {
            0 => OpenClosed {
                start,
                end: Box::new(endpoints[1].clone()),
            },
            1 => ClosedOpen {
                start,
                end: Box::new(endpoints[1].clone()),
            },
            2 => Open {
                start,
                end: Box::new(endpoints[1].clone()),
            },
            3 => PositiveInfinity { start },
            4 => NegativeInfinity { end: start },
            _ => unreachable!("validated integral kind"),
        }
    }
}

pub(super) fn prepare(
    rt: &mut Runtime,
    theorem: ImproperIntegralTheorem,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    let function_count = match theorem.rule {
        4 => 3,
        5 | 6 => 2,
        _ => 1,
    };
    let endpoint_count = if theorem.kind < 3 { 2 } else { 1 };
    let bounds = theorem.bounds(&args[function_count..function_count + endpoint_count]);
    let tail = &args[function_count + endpoint_count..];
    let integrals: Vec<_> = args[..function_count]
        .iter()
        .map(|f| ImproperIntegral::new(f.clone(), bounds.clone()))
        .collect();
    let mut requirements = Vec::new();
    for integral in &integrals {
        let Some(signature) = rt.improper_signature_requirements(
            integral,
            None,
            VerifyState::new(VerifyStateLevel::BuiltinRule),
        )?
        else {
            return Ok(Err(
                "requires a complete unary real function covering the integration region".into(),
            ));
        };
        requirements.extend(signature);
    }
    let integral = &integrals[0];
    let candidate = |rt: &mut Runtime, index: usize, value: Obj| -> Fact {
        rt.improper_predicate(&integrals[index], Some(value)).into()
    };
    let conclusions = match theorem.rule {
        0 => {
            requirements.push(member(rt, tail[0].clone(), real()).into());
            requirements
                .extend(rt.improper_definition_requirements(integral, Some(tail[0].clone())));
            vec![candidate(rt, 0, tail[0].clone())]
        }
        1 => {
            requirements.push(candidate(rt, 0, tail[0].clone()));
            rt.improper_definition_requirements(integral, Some(tail[0].clone()))
        }
        2 => {
            requirements.push(rt.improper_predicate(integral, None).into());
            vec![candidate(rt, 0, integral.clone().into())]
        }
        3 => {
            requirements.push(candidate(rt, 0, tail[0].clone()));
            requirements.push(candidate(rt, 0, tail[1].clone()));
            vec![eq(rt, tail[0].clone(), tail[1].clone()).into()]
        }
        4 => {
            requirements.push(candidate(rt, 0, tail[0].clone()));
            requirements.push(candidate(rt, 1, tail[1].clone()));
            let point = rt.fresh_internal_param();
            let value = id(&point);
            let equation = eq(
                rt,
                analysis_apply(args[2].clone(), value.clone()),
                add(
                    analysis_apply(args[0].clone(), value.clone()),
                    analysis_apply(args[1].clone(), value),
                ),
            );
            requirements.push(super::helper::forall(
                rt,
                point,
                integral_region(&bounds),
                vec![],
                vec![equation],
            ));
            vec![candidate(rt, 2, add(tail[0].clone(), tail[1].clone()))]
        }
        5 => {
            requirements.push(member(rt, tail[0].clone(), real()).into());
            requirements.push(candidate(rt, 0, tail[1].clone()));
            let point = rt.fresh_internal_param();
            let value = id(&point);
            let equation = eq(
                rt,
                analysis_apply(args[1].clone(), value.clone()),
                mul(tail[0].clone(), analysis_apply(args[0].clone(), value)),
            );
            requirements.push(super::helper::forall(
                rt,
                point,
                integral_region(&bounds),
                vec![],
                vec![equation],
            ));
            vec![candidate(rt, 1, mul(tail[0].clone(), tail[1].clone()))]
        }
        6 => {
            requirements.push(candidate(rt, 0, tail[0].clone()));
            let point = rt.fresh_internal_param();
            let value = id(&point);
            let equation = eq(
                rt,
                analysis_apply(args[0].clone(), value.clone()),
                analysis_apply(args[1].clone(), value),
            );
            requirements.push(super::helper::forall(
                rt,
                point,
                integral_region(&bounds),
                vec![],
                vec![equation],
            ));
            vec![candidate(rt, 1, tail[0].clone())]
        }
        7 => {
            requirements.push(candidate(rt, 0, tail[0].clone()));
            use ImproperIntegralBounds::*;
            let reversed = match bounds {
                OpenClosed { start, end } => ClosedOpen {
                    start: end,
                    end: start,
                },
                ClosedOpen { start, end } => OpenClosed {
                    start: end,
                    end: start,
                },
                Open { start, end } => Open {
                    start: end,
                    end: start,
                },
                _ => unreachable!("finite reversal"),
            };
            let reversed = ImproperIntegral::new(args[0].clone(), reversed);
            vec![rt
                .improper_predicate(&reversed, Some(sub(num("0"), tail[0].clone())))
                .into()]
        }
        _ => unreachable!("validated integral rule"),
    };
    Ok(Ok((requirements, conclusions)))
}
