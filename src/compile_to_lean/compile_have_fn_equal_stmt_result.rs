use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::{ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_have_fn_equal_statement(
        &self,
        result: &ExecHaveFnEqualStmtResult,
        position: &SourcePosition<'_>,
        _index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if local {
            return Err(LeanCompileError::unsupported("Function/LocalDeclaration"));
        }
        match result {
            ExecHaveFnEqualStmtResult::Success(proof) => {
                self.compile_have_fn_equal(proof, position)
            }
            ExecHaveFnEqualStmtResult::Failed(_) => Err(LeanCompileError::new(
                "Function/Failed",
                "Failed function formation is not compiler evidence.",
            )),
        }
    }

    fn compile_have_fn_equal(
        &self,
        proof: &ExecHaveFnEqualStmtSuccessResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let anonymous = Obj::FunctionSpace(FunctionSpace::AnonymousFn(
            proof.statement.equal_to_anonymous_fn.clone(),
        ));
        let fn_set = Obj::FunctionSpace(FunctionSpace::FnSet(
            proof.statement.equal_to_anonymous_fn.body.clone(),
        ));
        let anonymous_wd = success_object_wd(&proof.anonymous_fn_well_defined, &anonymous)?;
        let set_wd = success_object_wd(&proof.fn_set_well_defined, &fn_set)?;
        if anonymous_wd.obj() != &anonymous || set_wd.obj() != &fn_set {
            return Err(LeanCompileError::new(
                "Function/DeclarationWD",
                "The declaration must retain its exact original anonymous-function and signature subjects.",
            ));
        }
        let value = self.compile_wd(anonymous_wd, position)?;
        self.compile_wd(
            set_wd,
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;

        let stores = &proof.store_and_infer_result;
        let mut ids = stores.membership.stored_fact_ids();
        ids.extend(stores.defining_equal.stored_fact_ids());
        if stores.membership_fact_id != stores.membership.primary_fact_id()
            || stores.defining_equal_fact_id != stores.defining_equal.primary_fact_id()
            || stores.stored_fact_ids != ids
            || stores.membership_fact_id == stores.defining_equal_fact_id
        {
            return Err(LeanCompileError::new(
                "Function/StoreCapture",
                "The ordered function stores must match their membership/equality IDs and flattened ID view.",
            ));
        }
        let after_definition = SourcePosition {
            before: 2,
            ..*position
        };
        let after_member = SourcePosition {
            before: 3,
            ..*position
        };
        let membership = self.resolve_fact(stores.membership_fact_id, &after_member)?;
        let named_object = match &membership {
            Fact::AtomicFact(AtomicFact::InFact(member)) if member.set == fn_set => {
                match &member.element {
                    Obj::Identifier(IdentifierObj::Plain { id, name })
                        if *id == proof.statement.name.id && *name == proof.statement.name.name =>
                    {
                        &member.element
                    }
                    _ => {
                        return Err(LeanCompileError::new(
                            "Function/MembershipSubject",
                            "The captured function membership names another source declaration.",
                        ))
                    }
                }
            }
            _ => {
                return Err(LeanCompileError::new(
                    "Function/MembershipSubject",
                    "The captured membership has another source function signature.",
                ))
            }
        };
        self.validate_store(&stores.membership.store, &membership)?;
        let declaration = self.bind_alias(
            &proof.statement.name,
            named_object,
            &anonymous,
            &value,
            false,
            position,
        )?;
        let name = format!("_object_i{}", proof.statement.name.id.value());
        let object = self.context_application(&name, &after_definition);
        let member = (
            // Formation above checked this exact signature. Its stored field
            // avoids printing the complete domain/guard a second time.
            format!("Litex.In {object} (Litex.fnSet ({object}).val.signature)"),
            format!("(Litex.formulaFnInFnSet {object})"),
        );
        let member_declaration = self.emit_internal_fact(&membership, &member, &after_member)?;

        let after_equal = SourcePosition {
            before: 4,
            ..*position
        };
        let defining_equal = self.resolve_fact(stores.defining_equal_fact_id, &after_equal)?;
        alias_equality_subject(&defining_equal, &proof.statement.name, &anonymous)?;
        self.validate_store(&stores.defining_equal.store, &defining_equal)?;
        // The definition above is this exact checked anonymous object. Keep the
        // original equality citation, but refer to the definition on both sides
        // instead of elaborating its complete body a second time. Unfolding the
        // definition recovers the original stored right-hand side.
        let equal = (
            format!("Litex.Same {object} {object}"),
            format!("(Litex.sameRefl {object})"),
        );
        Ok(format!(
            "{declaration}\n{member_declaration}\n{}",
            self.emit_internal_fact(&defining_equal, &equal, &after_equal)?
        ))
    }
}
