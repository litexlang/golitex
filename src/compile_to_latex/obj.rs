use super::fact::quantifier_free;
use super::helper::{ident, identifier, name, operator, parens};
use crate::ast::obj::*;
use crate::launch_command::OutputLanguage;
use crate::module_manager::GlobalModuleManager;
use crate::runtime::RuntimeResult;

pub(super) fn obj(
    value: &Obj,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    expression(value, modules, lang, 0)
}

fn expression(
    value: &Obj,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
    parent: u8,
) -> RuntimeResult<String> {
    let o = |x: &Obj| obj(x, modules, lang);
    let e = |x: &Obj, p| expression(x, modules, lang, p);
    let (text, precedence) = match value {
        Obj::Identifier(x) => (identifier(x, modules)?, 50),
        Obj::Literal(x) => (
            match x {
                Literal::Number(n) => n.normalized_value.clone(),
                Literal::Pi(_) => r"\pi".into(),
                Literal::EulerNumber(_) => r"\mathrm{e}".into(),
                Literal::ImaginaryUnit(_) => r"\mathrm{i}".into(),
            },
            50,
        ),
        Obj::StandardSet(x) => (standard_set(x), 50),
        Obj::ArithmeticOperator(x) => match x {
            ArithmeticOperator::Add(x) => {
                (format!("{} + {}", e(&x.left, 10)?, e(&x.right, 11)?), 10)
            }
            ArithmeticOperator::Sub(x) => {
                (format!("{} - {}", e(&x.left, 10)?, e(&x.right, 11)?), 10)
            }
            ArithmeticOperator::Neg(x) => (format!("-{}", e(&x.arg, 31)?), 30),
            ArithmeticOperator::Mul(x) => (
                format!(r"{} \cdot {}", e(&x.left, 20)?, e(&x.right, 21)?),
                20,
            ),
            ArithmeticOperator::Div(x) => {
                (format!(r"\frac{{{}}}{{{}}}", o(&x.left)?, o(&x.right)?), 50)
            }
            ArithmeticOperator::Pow(x) => {
                (format!("{}^{{{}}}", e(&x.base, 41)?, o(&x.exponent)?), 40)
            }
            ArithmeticOperator::Abs(x) => (format!(r"\left|{}\right|", o(&x.arg)?), 50),
            ArithmeticOperator::Floor(x) => {
                (format!(r"\left\lfloor {}\right\rfloor", o(&x.arg)?), 50)
            }
            ArithmeticOperator::Ceil(x) => (format!(r"\left\lceil {}\right\rceil", o(&x.arg)?), 50),
            ArithmeticOperator::Min(x) => (operator("min", &[o(&x.left)?, o(&x.right)?]), 50),
            ArithmeticOperator::Max(x) => (operator("max", &[o(&x.left)?, o(&x.right)?]), 50),
            ArithmeticOperator::Sign(x) => (operator("sgn", &[o(&x.arg)?]), 50),
        },
        Obj::IntegerOperator(x) => (
            match x {
                IntegerOperator::Mod(x) => {
                    format!(r"{} \bmod {}", e(&x.left, 21)?, e(&x.right, 21)?)
                }
                IntegerOperator::Quot(x) => operator("quot", &[o(&x.left)?, o(&x.right)?]),
                IntegerOperator::Gcd(x) => operator("gcd", &[o(&x.left)?, o(&x.right)?]),
                IntegerOperator::Lcm(x) => operator("lcm", &[o(&x.left)?, o(&x.right)?]),
                IntegerOperator::Factorial(x) => format!("{}!", e(&x.arg, 51)?),
            },
            if matches!(x, IntegerOperator::Mod(_)) {
                20
            } else {
                50
            },
        ),
        Obj::TrigOperator(x) => (
            match x {
                TrigOperator::Sin(x) => operator("sin", &[o(&x.arg)?]),
                TrigOperator::Cos(x) => operator("cos", &[o(&x.arg)?]),
                TrigOperator::Tan(x) => operator("tan", &[o(&x.arg)?]),
                TrigOperator::Cot(x) => operator("cot", &[o(&x.arg)?]),
                TrigOperator::Arcsin(x) => operator("arcsin", &[o(&x.arg)?]),
                TrigOperator::Arccos(x) => operator("arccos", &[o(&x.arg)?]),
                TrigOperator::Arctan(x) => operator("arctan", &[o(&x.arg)?]),
                TrigOperator::Arccot(x) => operator("arccot", &[o(&x.arg)?]),
            },
            50,
        ),
        Obj::ExpLogOperator(x) => (
            match x {
                ExpLogOperator::Exp(x) => format!(r"\mathrm{{e}}^{{{}}}", o(&x.arg)?),
                ExpLogOperator::Ln(x) => operator("ln", &[o(&x.arg)?]),
                ExpLogOperator::Log(x) => {
                    format!(r"\log_{{{}}}{}", o(&x.base)?, parens(&o(&x.arg)?))
                }
                ExpLogOperator::Sqrt(x) => format!(r"\sqrt{{{}}}", o(&x.arg)?),
            },
            50,
        ),
        Obj::ComplexOperator(x) => (
            match x {
                ComplexOperator::RealPart(x) => operator("Re", &[o(&x.arg)?]),
                ComplexOperator::ImaginaryPart(x) => operator("Im", &[o(&x.arg)?]),
                ComplexOperator::ComplexAbs(x) => format!(r"\left|{}\right|", o(&x.arg)?),
            },
            50,
        ),
        Obj::SetOperator(x) => match x {
            SetOperator::Union(x) => (
                format!(r"{} \cup {}", e(&x.left, 10)?, e(&x.right, 11)?),
                10,
            ),
            SetOperator::Intersect(x) => (
                format!(r"{} \cap {}", e(&x.left, 20)?, e(&x.right, 21)?),
                20,
            ),
            SetOperator::SetMinus(x) => (
                format!(r"{} \setminus {}", e(&x.left, 20)?, e(&x.right, 21)?),
                20,
            ),
            SetOperator::FamilyUnion(x) => (format!(r"\bigcup {}", parens(&o(&x.left)?)), 50),
            SetOperator::FamilyIntersect(x) => (format!(r"\bigcap {}", parens(&o(&x.left)?)), 50),
            SetOperator::PowerSet(x) => (format!(r"\mathcal{{P}}{}", parens(&o(&x.set)?)), 50),
            // Keep the ambient set, particularly for an empty indexed intersection.
            SetOperator::IndexUnion(x) => (
                format!(
                    r"\left\{{\xi\in {}\;\middle|\;\exists\iota\in {},\ \xi\in {}(\iota)\right\}}",
                    o(&x.ambient_set)?,
                    o(&x.index_set)?,
                    e(&x.family_fn, 51)?
                ),
                50,
            ),
            SetOperator::IndexIntersect(x) => (
                format!(
                    r"\left\{{\xi\in {}\;\middle|\;\forall\iota\in {},\ \xi\in {}(\iota)\right\}}",
                    o(&x.ambient_set)?,
                    o(&x.index_set)?,
                    e(&x.family_fn, 51)?
                ),
                50,
            ),
            SetOperator::IndexCart(x) => (
                operator(
                    "IndexCart",
                    &[o(&x.index_set)?, o(&x.family_set)?, o(&x.family_fn)?],
                ),
                50,
            ),
        },
        Obj::SetFormer(x) => (
            match x {
                SetFormer::ListSet(x) => {
                    let mut items = Vec::new();
                    for y in &x.list {
                        items.push(o(y)?);
                    }
                    format!(r"\left\{{{}\right\}}", items.join(", "))
                }
                SetFormer::SetBuilder(x) => {
                    let mut facts = Vec::new();
                    for f in &x.facts {
                        facts.push(parens(&quantifier_free(f, modules, lang)?));
                    }
                    format!(
                        r"\left\{{{}\in {}\;\middle|\;{}\right\}}",
                        ident(&x.param_binding.name),
                        o(&x.param_set)?,
                        facts.join(r" \land ")
                    )
                }
                SetFormer::Range(x) => integer_range(&o(&x.start)?, &o(&x.end)?, false),
                SetFormer::ClosedRange(x) => integer_range(&o(&x.start)?, &o(&x.end)?, true),
                SetFormer::SeqSet(x) => format!(r"{}^{{\mathbb{{N}}_{{>0}}}}", e(&x.set, 51)?),
                SetFormer::FiniteSeqSet(x) => {
                    format!(
                        r"{}^{{\{{\iota\in\mathbb{{N}}_{{>0}}\mid\iota\leq {}\}}}}",
                        e(&x.set, 51)?,
                        o(&x.n)?
                    )
                }
                SetFormer::IntervalObj(x) => match x {
                    IntervalObj::LeftOpenRightOpen(x) => {
                        format!("({}, {})", o(&x.start)?, o(&x.end)?)
                    }
                    IntervalObj::LeftOpenRightClosed(x) => {
                        format!("({}, {}]", o(&x.start)?, o(&x.end)?)
                    }
                    IntervalObj::LeftClosedRightOpen(x) => {
                        format!("[{}, {})", o(&x.start)?, o(&x.end)?)
                    }
                    IntervalObj::LeftClosedRightClosed(x) => {
                        format!("[{}, {}]", o(&x.start)?, o(&x.end)?)
                    }
                },
                SetFormer::OneSideInfinityIntervalObj(x) => match x {
                    OneSideInfinityIntervalObj::LowerOpen(x) => {
                        format!(r"({},+\infty)", o(&x.start)?)
                    }
                    OneSideInfinityIntervalObj::LowerClosed(x) => {
                        format!(r"[{},+\infty)", o(&x.start)?)
                    }
                    OneSideInfinityIntervalObj::UpperOpen(x) => {
                        format!(r"(-\infty,{})", o(&x.start)?)
                    }
                    OneSideInfinityIntervalObj::UpperClosed(x) => {
                        format!(r"(-\infty,{}]", o(&x.start)?)
                    }
                },
            },
            50,
        ),
        Obj::ProductShape(x) => match x {
            ProductShape::Cart(x) => {
                let mut items = Vec::new();
                for y in &x.args {
                    items.push(e(y, 21)?);
                }
                (
                    if items.is_empty() {
                        r"\{()\}".into()
                    } else {
                        items.join(r" \times ")
                    },
                    20,
                )
            }
            ProductShape::Tuple(x) => {
                let mut items = Vec::new();
                for y in &x.args {
                    items.push(o(y)?);
                }
                (parens(&items.join(", ")), 50)
            }
        },
        Obj::FunctionSpace(x) => (
            match x {
                FunctionSpace::FnSet(x) => parens(&fn_set(x, modules, lang)?),
                FunctionSpace::AnonymousFn(x) => anonymous(x, modules, lang)?,
                FunctionSpace::FnRange(x) => operator("range", &[o(&x.function)?]),
            },
            50,
        ),
        Obj::FnObj(x) => {
            let mut head = match x.head.as_ref() {
                FnObjHead::Object(value) => parens(&obj(value, modules, lang)?),
                FnObjHead::Identifier(x) => identifier(x, modules)?,
                FnObjHead::AnonymousFnLiteral(x) => parens(&anonymous(x, modules, lang)?),
                FnObjHead::FieldAccess(x) => field_access(x, modules, lang)?,
                FnObjHead::InstantiatedTemplateObj(x) => template(x, modules, lang)?,
            };
            for group in &x.body {
                let mut args = Vec::new();
                for arg in group {
                    args.push(o(arg)?);
                }
                head.push_str(&parens(&args.join(", ")));
            }
            (head, 50)
        }
        Obj::IteratedOperator(x) => (
            match x {
                // Greek generated indices cannot collide with ASCII Litex identifiers.
                IteratedOperator::Sum(x) => format!(
                    r"\sum_{{\iota={}}}^{{{}}} {}(\iota)",
                    o(&x.start)?,
                    o(&x.end)?,
                    e(&x.func, 51)?
                ),
                IteratedOperator::Product(x) => format!(
                    r"\prod_{{\iota={}}}^{{{}}} {}(\iota)",
                    o(&x.start)?,
                    o(&x.end)?,
                    e(&x.func, 51)?
                ),
                IteratedOperator::SumOfFiniteSet(x) => format!(
                    r"\sum_{{\iota\in {}}} {}(\iota)",
                    o(&x.set)?,
                    e(&x.func, 51)?
                ),
                IteratedOperator::ProductOfFiniteSet(x) => format!(
                    r"\prod_{{\iota\in {}}} {}(\iota)",
                    o(&x.set)?,
                    e(&x.func, 51)?
                ),
                IteratedOperator::Reduce(x) => operator(
                    "reduce",
                    &[
                        o(&x.start)?,
                        o(&x.end)?,
                        o(&x.func)?,
                        o(&x.op)?,
                        o(&x.seed)?,
                    ],
                ),
                IteratedOperator::FiniteSetReduce(x) => operator(
                    "finiteReduce",
                    &[o(&x.set)?, o(&x.func)?, o(&x.op)?, o(&x.seed)?],
                ),
            },
            30,
        ),
        Obj::FiniteSetStat(x) => (
            match x {
                FiniteSetStat::FiniteSetSize(x) => format!(r"\left|{}\right|", o(&x.set)?),
                FiniteSetStat::FiniteSetMax(x) => operator("max", &[o(&x.set)?]),
                FiniteSetStat::FiniteSetMin(x) => operator("min", &[o(&x.set)?]),
            },
            50,
        ),
        Obj::StructAndFieldAccessObj(x) => (
            match x {
                StructAndFieldAccessObj::StructObj(x) => {
                    let n = name(&x.name, modules)?;
                    let mut args = Vec::new();
                    for arg in &x.params {
                        args.push(o(arg)?);
                    }
                    if args.is_empty() {
                        n
                    } else {
                        format!(r"{}\langle {}\rangle", n, args.join(", "))
                    }
                }
                StructAndFieldAccessObj::FieldAccess(x) => field_access(x, modules, lang)?,
            },
            50,
        ),
        Obj::InstantiatedTemplateObj(x) => (template(x, modules, lang)?, 50),
    };
    Ok(if precedence < parent {
        parens(&text)
    } else {
        text
    })
}

pub(super) fn fn_set(
    value: &FnSet,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    function_space(
        &value.set_bound_parameters,
        &value.dom_facts,
        &value.ret_set,
        modules,
        lang,
    )
}

pub(super) fn function_space(
    params: &crate::ast::param::SetBoundParameterList,
    dom: &[crate::ast::fact::QuantifierFreeFact],
    ret: &Obj,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut carriers = Vec::new();
    let mut names = Vec::new();
    for group in &params.groups {
        for param in &group.params {
            carriers.push(expression(&group.param_type, modules, lang, 21)?);
            names.push(ident(&param.name));
        }
    }
    let mut domain = carriers.join(r" \times ");
    if carriers.is_empty() {
        domain = r"\{()\}".into();
    }
    if !dom.is_empty() {
        let mut conditions = Vec::new();
        for f in dom {
            conditions.push(parens(&quantifier_free(f, modules, lang)?));
        }
        let binding = if names.len() == 1 {
            names[0].clone()
        } else {
            parens(&names.join(", "))
        };
        domain = format!(
            r"\left\{{{}\in {}\;\middle|\;{}\right\}}",
            binding,
            domain,
            conditions.join(r" \land ")
        );
    }
    if carriers.len() > 1 && dom.is_empty() {
        domain = parens(&domain);
    }
    Ok(format!(r"{}\to {}", domain, obj(ret, modules, lang)?))
}

pub(super) fn anonymous(
    value: &AnonymousFn,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut params = Vec::new();
    for g in &value.body.set_bound_parameters.groups {
        for p in &g.params {
            params.push(ident(&p.name));
        }
    }
    Ok(format!(
        r"\left[\begin{{array}}{{c}}{}\\{}\mapsto {}\end{{array}}\right]",
        fn_set(&value.body, modules, lang)?,
        parens(&params.join(", ")),
        obj(&value.equal_to, modules, lang)?
    ))
}

fn field_access(
    value: &FieldAccess,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut text = expression(&value.obj, modules, lang, 51)?;
    for field in &value.fields {
        text.push_str(&format!(".{}", ident(field)));
    }
    Ok(text)
}
fn template(
    value: &InstantiatedTemplateObj,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut args = Vec::new();
    for arg in &value.args {
        args.push(obj(arg, modules, lang)?);
    }
    Ok(format!(
        r"{}\langle {}\rangle",
        name(&value.template_name, modules)?,
        args.join(", ")
    ))
}
fn integer_range(start: &str, end: &str, closed: bool) -> String {
    let relation = if closed { r"\leq" } else { "<" };
    format!(r"\left\{{\iota\in\mathbb{{Z}}\;\middle|\;{start}\leq\iota {relation} {end}\right\}}")
}
fn standard_set(value: &StandardSet) -> String {
    let (letter, suffix) = match value {
        StandardSet::N => ("N", ""),
        StandardSet::Z => ("Z", ""),
        StandardSet::Q => ("Q", ""),
        StandardSet::R => ("R", ""),
        StandardSet::C => ("C", ""),
        StandardSet::NPos => ("N", ">0"),
        StandardSet::QPos => ("Q", ">0"),
        StandardSet::RPos => ("R", ">0"),
        StandardSet::ZNeg => ("Z", "<0"),
        StandardSet::QNeg => ("Q", "<0"),
        StandardSet::RNeg => ("R", "<0"),
        StandardSet::ZStar => ("Z", r"\ne0"),
        StandardSet::QStar => ("Q", r"\ne0"),
        StandardSet::RStar => ("R", r"\ne0"),
        StandardSet::CStar => ("C", r"\ne0"),
    };
    if suffix.is_empty() {
        format!(r"\mathbb{{{letter}}}")
    } else {
        format!(r"\mathbb{{{letter}}}_{{{suffix}}}")
    }
}
