use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::AtomicExceptEqualityFactSearchProofByBuiltinRule;
use crate::runtime::FactId;

pub(super) fn cite_from_atomic_builtin_rule(
    rule: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
) -> Option<FactId> {
    match rule {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::BijectiveFact(bf) => bf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::CoprimeFact(cf) => cf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::DvdFact(df) => df.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(gef) => {
            gef.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(gf) => gf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(if_) => if_.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InjectiveFact(if_) => if_.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsChoiceFunctionForFact(icfff) => {
            icfff.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(ifsf) => {
            ifsf.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(insf) => {
            insf.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsSetFact(isf) => isf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(lef) => lef.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(lf) => lf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NormalAtomicFact(naf) => {
            naf.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotBijectiveFact(nbf) => {
            nbf.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotCoprimeFact(ncf) => ncf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotDvdFact(ndf) => ndf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(nef) => nef.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterEqualFact(ngef) => {
            ngef.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact(ngf) => ngf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(nif) => nif.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInjectiveFact(nif) => {
            nif.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsChoiceFunctionForFact(nicfff) => {
            nicfff.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsFiniteSetFact(nifsf) => {
            nifsf.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsNonemptySetFact(ninsf) => {
            ninsf.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsSetFact(nisf) => nisf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessEqualFact(nlef) => {
            nlef.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessFact(nlf) => nlf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotNormalAtomicFact(nnaf) => {
            nnaf.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotPrimeFact(npf) => npf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotProperSubsetFact(npsf) => {
            npsf.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotProperSupersetFact(npsf) => {
            npsf.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSubsetFact(nsf) => nsf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSupersetFact(nsf) => {
            nsf.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSurjectiveFact(nsf) => {
            nsf.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::PrimeFact(pf) => pf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::ProperSubsetFact(psf) => {
            psf.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::ProperSupersetFact(psf) => {
            psf.cite_fact_id()
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(sf) => sf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SupersetFact(sf) => sf.cite_fact_id(),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SurjectiveFact(sf) => sf.cite_fact_id(),
    }
}
