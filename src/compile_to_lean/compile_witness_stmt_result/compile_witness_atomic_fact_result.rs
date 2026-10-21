use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_witness_stmt::ExecWitnessAtomicFactStmtSuccessResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_witness_atomic_statement(
        &self,
        proof: &ExecWitnessAtomicFactStmtSuccessResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let normal = &proof.statement.atomic_fact;
        let (declaration, _, _) = position.visible_prop(&normal.predicate)?;
        let substitution = self.prop_argument_substitution(declaration, normal)?;
        let clauses = &declaration.statement.iff_facts;
        if clauses.len() != 1
            || !matches!(&clauses[0], Fact::ExistFact(_))
            || !matches!(&proof.projected_exist, ExistShapedFact::Exist(_))
            || !instantiated_fact_matches(
                &clauses[0],
                &crate::ast::fact::exist_shaped_fact_to_fact(&proof.projected_exist),
                &substitution,
            )
        {
            return Err(LeanCompileError::new("Witness/PropProjection", "The witness must instantiate the declared predicate's sole ordinary existential clause."));
        }
        let parameters = declaration
            .statement
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
            .collect::<Vec<_>>();
        if proof.prop_argument_type_checks.len() != parameters.len() {
            return Err(LeanCompileError::new(
                "Witness/PropArguments",
                "Every source predicate argument needs its original ordered type check.",
            ));
        }
        let mut members = Vec::new();
        for (i, ((_, param_type), check)) in parameters
            .iter()
            .zip(&proof.prop_argument_type_checks)
            .enumerate()
        {
            let actual = source_subject(check)?;
            match (param_type, &actual) {
                (ParamType::Obj(set), Fact::AtomicFact(AtomicFact::InFact(member)))
                    if member.element == normal.body[i]
                        && instantiated_object_matches(set, &member.set, &substitution) => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "Witness/PropArguments",
                        "A predicate argument check has another subject, carrier or position.",
                    ))
                }
            }
            let prior = SourcePosition {
                before: i,
                ..*position
            };
            members.push(self.compile_verify(check, &prior)?.1);
        }
        let (_, body) = self.compile_witness_body(SourceOwner::WitnessAtomic(proof), position)?;
        let mut folded = format!("({body})");
        for member in members.into_iter().rev() {
            folded = format!("(Exists.intro {member} {folded})");
        }
        let complete = SourcePosition {
            before: proof.prop_argument_type_checks.len() + 1 + proof.statement.witnesses.len() * 2,
            ..*position
        };
        let fact = Fact::AtomicFact(AtomicFact::NormalAtomicFact(normal.clone()));
        let proposition = self.fact_proposition(&fact, &complete)?;
        self.compile_completed_fact_statement(
            &fact,
            (proposition, folded),
            &proof.store_and_infer_result,
            &complete,
            index,
            local,
        )
    }
}
