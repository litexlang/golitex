use super::compile_finite_function::coordinate_membership;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::known_tuple::literal_positive_usize;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// Continue the selected call's original WD with its Cartesian return.
    /// The child and requirement offsets refer to the same original result.
    pub(super) fn compile_returned_cart_call(
        &self,
        application: &FnObj,
        proof: &FnObjObjWellDefinedProof,
        receiver: &str,
        output: &Obj,
        receiver_member: &str,
        child_index: usize,
        requirement_index: usize,
        position: &SourcePosition<'_>,
    ) -> Result<(String, Obj, String), LeanCompileError> {
        let Obj::ProductShape(ProductShape::Cart(cart)) = output else {
            return Err(LeanCompileError::unsupported("ReturnedCart/Carrier"));
        };
        let argument = &application.body[1][0];
        let index = literal_positive_usize(argument)
            .ok_or_else(|| LeanCompileError::unsupported("ReturnedCart/VariableCoordinate"))?;
        let factor = cart.args.get(index - 1).ok_or_else(|| {
            LeanCompileError::new(
                "ReturnedCart/Index",
                "The coordinate is outside the returned Cartesian domain.",
            )
        })?;
        let child = &proof.child_obj_well_defined[child_index];
        ensure_object(argument, child)?;
        let argument_term = self.compile_wd(
            child,
            &SourcePosition {
                before: child_index,
                ..*position
            },
        )?;
        let requirement = &proof.requirement_fact_verified[requirement_index];
        let Fact::AtomicFact(AtomicFact::InFact(domain_member)) = source_subject(requirement)?
        else {
            return Err(LeanCompileError::new(
                "ReturnedCart/Domain",
                "The next call layer needs its original index membership.",
            ));
        };
        let n = cart.args.len();
        if domain_member.element.ir() != argument.ir()
            || !matches!(&domain_member.set, Obj::SetFormer(SetFormer::ClosedRange(range))
                if closed_integer(&range.start) == Some(1)
                    && closed_integer(&range.end) == Some(n as i128))
        {
            return Err(LeanCompileError::new(
                "ReturnedCart/Domain",
                "The next layer must retain its exact argument and complete one-based domain.",
            ));
        }
        let domain_position = SourcePosition {
            before: proof.child_obj_well_defined.len() + requirement_index,
            ..*position
        };
        let domain_proof = self.compile_verify(requirement, &domain_position)?.1;
        let formed = SourcePosition {
            before: domain_position.before + 1,
            ..domain_position
        };
        let cart_term = self.compile_object_reference(output, &formed)?;
        let range = self.compile_object_reference(&domain_member.set, &formed)?;
        let factor_term = self.compile_object_reference(factor, &formed)?;
        let setup = format!(
            "let _receiver := {receiver}\nlet _argument := {argument_term}\nlet _cart := {cart_term}\nhave _cartMember : Litex.In _receiver _cart := {receiver_member}"
        );
        let call_body = format!(
            "{setup}\nlet _sourceRange := {range}\nhave _indexMember : M.mem (Litex.denote _argument) (Litex.FiniteFunction.indexSet {n}) := by\n  have _source := {domain_proof}\n  change M.mem (Litex.denote _argument) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (({n} : ℕ) : ℂ)) _sourceRange.wd.1 _sourceRange.wd.2)) at _source\n  rw [Litex.closedRange_indexSet] at _source\n  exact _source\nexact Litex.cartCall _receiver _cart _argument _cartMember _indexMember"
        );
        let call = format!("(by\n  {}\n)", call_body.replace('\n', "\n  "));
        let coordinate =
            coordinate_membership("_receiver", &factor_term, "_cartMember", index - 1, n);
        let member_body = format!("{setup}\nexact {coordinate}");
        let member = format!(
            "(show Litex.In {call} {factor_term} from by\n  {}\n)",
            member_body.replace('\n', "\n  ")
        );
        Ok((call, factor.as_ref().clone(), member))
    }
}
