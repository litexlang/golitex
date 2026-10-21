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
        self.compile_object_reference(&domain_member.set, &formed)?;
        let factor_term = self.compile_object_reference(factor, &formed)?;
        // A Cartesian return uses the generic CallOn constructor. Its first
        // stage has already replayed every domain proof; use that same call's
        // output law without printing the receiver construction again.
        let setup = format!(
            "let _receiver := {receiver}\nlet _argument := {argument_term}\nlet _cart := {cart_term}\nhave _cartMember : Litex.In _receiver _cart := Litex.callOnInOutput _receiver"
        );
        let call = match position.bound_fn_call(application, proof) {
            Some(call) => call,
            None => {
                let body = format!(
                    "{setup}\nhave _indexMember : M.mem (Litex.denote _argument) (Litex.FiniteFunction.indexSet {n}) := Litex.indexSetMemberOfClosedRange {domain_proof}\nexact Litex.cartCall _receiver _cart _argument _cartMember _indexMember"
                );
                format!("(by\n  {}\n)", body.replace('\n', "\n  "))
            }
        };
        let coordinate = coordinate_membership("_cartMember", index - 1, n);
        let member_body = format!("{setup}\nexact {coordinate}");
        let member = format!(
            "(show Litex.In {call} {factor_term} from by\n  {}\n)",
            member_body.replace('\n', "\n  ")
        );
        Ok((call, factor.as_ref().clone(), member))
    }
}
