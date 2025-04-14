// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_ast

func NewTopStmt(stmt Stmt, isPub bool) *TopStmt {
	return &TopStmt{stmt, isPub}
}

func NewDefObjStmt(objs []string, objSets []Fc, facts []FactStmt) *DefObjStmt {
	return &DefObjStmt{objs, objSets, facts}
}

func NewDefInterfaceStmt() *DefInterfaceStmt {
	return &DefInterfaceStmt{}
}

func NewDefTypeStmt() *DefTypeStmt {
	return &DefTypeStmt{}
}

func NewDefConPropStmt(defHeader ConDefHeader, domFacts []FactStmt, iffFacts []*SpecFactStmt) *DefConPropStmt {
	return &DefConPropStmt{defHeader, domFacts, iffFacts}
}

func NewDefConExistPropStmt(defHeader ConDefHeader, existFc []string, existFcTypes []*FcAtom, thenFacts []FactStmt) *DefConExistPropStmt {
	return &DefConExistPropStmt{defHeader, existFc, existFcTypes, thenFacts}
}

func NewDefConFnStmt(defHeader ConDefHeader, retType Fc, domFacts []FactStmt, thenFacts []*SpecFactStmt) *DefConFnStmt {
	return &DefConFnStmt{defHeader, retType, domFacts, thenFacts}
}

func NewUniFactStmt(params []string, paramTypes []Fc, domFacts []FactStmt, thenFacts []*SpecFactStmt) *ConUniFactStmt {
	return &ConUniFactStmt{params, paramTypes, domFacts, thenFacts}
}

func NewGenericUniStmt(typeParams []string, typeInterfaces []*FcAtom, params []string, paramTypes []Fc, domFacts []FactStmt, thenFacts []*SpecFactStmt) *GenUniStmt {
	return &GenUniStmt{typeParams, typeInterfaces, params, paramTypes, domFacts, thenFacts}
}

func NewSpecFactStmt(isTrue bool, propName FcAtom, params []Fc) *SpecFactStmt {
	return &SpecFactStmt{isTrue, propName, params}
}

func NewClaimProveStmt(proveTrue bool, toCheckFacts []FactStmt, proofs []Stmt) *ClaimProveStmt {
	return &ClaimProveStmt{proveTrue, toCheckFacts, proofs}
}

func NewKnowStmt(facts []FactStmt) *KnowStmt {
	return &KnowStmt{facts}
}

func NewHaveStmt(propStmt SpecFactStmt, member []string) *HaveStmt {
	return &HaveStmt{propStmt, member}
}

func NewAxiomStmt(decl DefPropOrExistPropStmt) *AxiomStmt {
	return &AxiomStmt{decl}
}

func NewThmStmt(decl DefPropOrExistPropStmt, proof []Stmt) *ThmStmt {
	return &ThmStmt{decl, proof}
}

func NewCondFactStmt(condFacts []FactStmt, thenFacts []*SpecFactStmt) *CondFactStmt {
	return &CondFactStmt{condFacts, thenFacts}
}

func NewFcFnDecl(name string, params []string) *FcFnDecl {
	return &FcFnDecl{name, params}
}

func NewConDefHeader(name string, params []string, typeParams []Fc) *ConDefHeader {
	return &ConDefHeader{name, params, typeParams}
}

func NewExistFactStmt(isTrue bool, propName FcAtom, params []Fc, existFc []Fc) *ExistFactStmt {
	return &ExistFactStmt{isTrue, propName, params, existFc}
}
