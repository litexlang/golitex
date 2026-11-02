//! Mathematical matrix notation. Bracketed size subscripts retain explicit
//! source dimension parameters; matrix entry access is still application.
use super::helper::call_parens;
use super::obj::{expression, obj};
use crate::ast::obj::{MatrixOperator, Obj};
use crate::launch_command::OutputLanguage;
use crate::module_manager::GlobalModuleManager;
use crate::runtime::RuntimeResult;

fn sized(text: String, dimensions: Vec<String>) -> String {
    super::helper::dimensioned(text, &dimensions)
}

pub(super) fn matrix(
    value: &MatrixOperator,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let o = |x: &Obj| obj(x, modules, lang);
    let e = |x: &Obj, p| expression(x, modules, lang, p);
    Ok(match value {
        MatrixOperator::Determinant(x) => {
            format!(r"\det_{{{}}}{}", o(&x.order)?, call_parens(&o(&x.matrix)?))
        }
        MatrixOperator::ZeroMatrix(x) => format!(r"0_{{{}\times {}}}", o(&x.rows)?, o(&x.cols)?),
        MatrixOperator::IdentityMatrix(x) => format!(r"I_{{{}}}", o(&x.order)?),
        MatrixOperator::Transpose(x) => sized(
            format!(r"{}^{{\mathsf{{T}}}}", e(&x.matrix, 41)?),
            vec![o(&x.rows)?, o(&x.cols)?],
        ),
        MatrixOperator::ConjugateTranspose(x) => sized(
            format!(r"{}^{{\mathsf{{H}}}}", e(&x.matrix, 41)?),
            vec![o(&x.rows)?, o(&x.cols)?],
        ),
        MatrixOperator::Trace(x) => format!(
            r"\operatorname{{tr}}_{{{}}}{}",
            o(&x.order)?,
            call_parens(&o(&x.matrix)?)
        ),
        MatrixOperator::Add(x) => sized(
            format!("{} + {}", e(&x.left, 10)?, e(&x.right, 11)?),
            vec![o(&x.rows)?, o(&x.cols)?],
        ),
        MatrixOperator::Subtract(x) => sized(
            format!("{} - {}", e(&x.left, 10)?, e(&x.right, 11)?),
            vec![o(&x.rows)?, o(&x.cols)?],
        ),
        MatrixOperator::Scale(x) => sized(
            format!(r"{}\,{}", e(&x.scalar, 21)?, e(&x.matrix, 21)?),
            vec![o(&x.rows)?, o(&x.cols)?],
        ),
        MatrixOperator::Multiply(x) => sized(
            format!(r"{}\,{}", e(&x.left, 21)?, e(&x.right, 21)?),
            vec![o(&x.rows)?, o(&x.inner)?, o(&x.cols)?],
        ),
        MatrixOperator::Apply(x) => sized(
            format!(r"{}\,{}", e(&x.matrix, 21)?, e(&x.vector, 21)?),
            vec![o(&x.rows)?, o(&x.cols)?],
        ),
        MatrixOperator::Power(x) => sized(
            format!(r"{}^{{{}}}", e(&x.matrix, 41)?, o(&x.exponent)?),
            vec![o(&x.order)?],
        ),
        MatrixOperator::Inverse(x) => {
            sized(format!(r"{}^{{-1}}", e(&x.matrix, 41)?), vec![o(&x.order)?])
        }
        MatrixOperator::Rank(x) => format!(
            r"\operatorname{{rank}}_{{[{},{}]}}{}",
            o(&x.rows)?,
            o(&x.cols)?,
            call_parens(&o(&x.matrix)?)
        ),
        MatrixOperator::Minor(x) => format!(
            r"{}_{{\widehat{{{}}},\widehat{{{}}}}}^{{[{}]}}",
            e(&x.matrix, 51)?,
            o(&x.row)?,
            o(&x.col)?,
            o(&x.order)?
        ),
        MatrixOperator::Cofactor(x) => format!(
            r"\operatorname{{cof}}_{{{},{}}}^{{[{}]}}{}",
            o(&x.row)?,
            o(&x.col)?,
            o(&x.order)?,
            call_parens(&o(&x.matrix)?)
        ),
        MatrixOperator::Adjugate(x) => format!(
            r"\operatorname{{adj}}_{{{}}}{}",
            o(&x.order)?,
            call_parens(&o(&x.matrix)?)
        ),
        MatrixOperator::Diagonal(x) => format!(
            r"\operatorname{{diag}}_{{{}}}{}",
            o(&x.order)?,
            call_parens(&o(&x.vector)?)
        ),
        MatrixOperator::OuterProduct(x) => sized(
            format!(
                r"{}\,{}^{{\mathsf{{T}}}}",
                e(&x.left, 21)?,
                e(&x.right, 41)?
            ),
            vec![o(&x.rows)?, o(&x.cols)?],
        ),
        MatrixOperator::InnerProduct(x) => format!(
            r"\left\langle {},{}\right\rangle_{{[{}]}}",
            o(&x.left)?,
            o(&x.right)?,
            o(&x.dimension)?
        ),
        MatrixOperator::EuclideanNorm(x) => format!(
            r"\left\|{}\right\|_{{2,[{}]}}",
            o(&x.vector)?,
            o(&x.dimension)?
        ),
        MatrixOperator::FrobeniusNorm(x) => format!(
            r"\left\|{}\right\|_{{\mathrm{{F}},[{},{}]}}",
            o(&x.matrix)?,
            o(&x.rows)?,
            o(&x.cols)?
        ),
    })
}
