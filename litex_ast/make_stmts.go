package litexast

func MakeTopStmt(stmt Stmt, isPub bool) *TopStmt {
	return &TopStmt{stmt, isPub}
}

func MakeDefObjStmt(objs []string, objSets []Fc, facts []FactStmt) *DefObjStmt {
	return &DefObjStmt{objs, objSets, facts}
}

func MakeDefInterfaceStmt() *DefInterfaceStmt {
	return &DefInterfaceStmt{}
}

func MakeDefTypeStmt() *DefTypeStmt {
	return &DefTypeStmt{}
}

func MakeDefConPropStmt(defHeader ConDefHeader, domFacts []FactStmt, iffFacts []*SpecFactStmt) *DefConPropStmt {
	return &DefConPropStmt{defHeader, domFacts, iffFacts}
}

func MakeDefConExistPropStmt(defHeader ConDefHeader, existFc []string, existFcTypes []*FcAtom, domFacts []FactStmt, thenFacts []FactStmt) *DefConExistPropStmt {
	return &DefConExistPropStmt{defHeader, existFc, existFcTypes, domFacts, thenFacts}
}

func MakeDefConFnStmt(defHeader ConDefHeader, retType Fc, domFacts []FactStmt, thenFacts []*SpecFactStmt) *DefConFnStmt {
	return &DefConFnStmt{defHeader, retType, domFacts, thenFacts}
}

func MakeUniFactStmt(params []string, paramTypes []Fc, domFacts []FactStmt, thenFacts []*SpecFactStmt) *UniFactStmt {
	return &UniFactStmt{params, paramTypes, domFacts, thenFacts}
}

func MakeGenericUniStmt(typeParams []string, typeInterfaces []*FcAtom, params []string, paramTypes []Fc, domFacts []FactStmt, thenFacts []*SpecFactStmt) *GenericUniStmt {
	return &GenericUniStmt{typeParams, typeInterfaces, params, paramTypes, domFacts, thenFacts}
}

func MakeSpecFactStmt(isTrue bool, propName FcAtom, params []Fc) *SpecFactStmt {
	return &SpecFactStmt{isTrue, propName, params}
}

func MakeClaimProveByContradictStmt(toCheck []FactStmt, proof []Stmt) *ClaimProveByContradictStmt {
	return &ClaimProveByContradictStmt{toCheck, proof}
}

func MakeClaimProveStmt(toCheckFacts []FactStmt, proofs []Stmt) *ClaimProveStmt {
	return &ClaimProveStmt{toCheckFacts, proofs}
}

func MakeKnowStmt(facts []FactStmt) *KnowStmt {
	return &KnowStmt{facts}
}

func MakeHaveStmt(propStmt SpecFactStmt, member []string) *HaveStmt {
	return &HaveStmt{propStmt, member}
}

func MakeAxiomStmt(decl DefPropStmt) *AxiomStmt {
	return &AxiomStmt{decl}
}

func MakeThmStmt(decl DefPropStmt, proof []Stmt) *ThmStmt {
	return &ThmStmt{decl, proof}
}

func MakeCondFactStmt(condFacts []FactStmt, thenFacts []*SpecFactStmt) *CondFactStmt {
	return &CondFactStmt{condFacts, thenFacts}
}

func MakeFcFnDecl(name string, params []string) *FcFnDecl {
	return &FcFnDecl{name, params}
}

func MakeConDefHeader(name string, params []string, typeParams []Fc) *ConDefHeader {
	return &ConDefHeader{name, params, typeParams}
}
