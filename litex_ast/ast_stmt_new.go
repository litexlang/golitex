// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

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

func NewDefConPropStmt(defHeader ConDefHeader, domFacts []FactStmt, iffFacts []FactStmt) *DefConPropStmt {
	return &DefConPropStmt{defHeader, domFacts, iffFacts}
}

func NewDefConExistPropStmt(def *ExistPropDef, existParams []string, existParamSets []Fc) *DefConExistPropStmt {
	return &DefConExistPropStmt{*def, existParams, existParamSets}
}

func NewDefConFnStmt(defHeader ConDefHeader, retType Fc, domFacts []FactStmt, thenFacts []FactStmt) *DefConFnStmt {
	return &DefConFnStmt{defHeader, retType, domFacts, thenFacts}
}

func newConUniFactStmt(params []string, paramTypes []Fc, domFacts []FactStmt, thenFacts []FactStmt, iffFacts []FactStmt) *ConUniFactStmt {
	return &ConUniFactStmt{params, paramTypes, domFacts, thenFacts, iffFacts}
}

func NewSpecFactStmt(typeEnum SpecFactEnum, propName FcAtom, params []Fc) *SpecFactStmt {
	return &SpecFactStmt{typeEnum, propName, params}
}

func NewClaimProveStmt(proveTrue bool, toCheckFact FactStmt, proofs []Stmt) *ClaimStmt {
	return &ClaimStmt{proveTrue, toCheckFact, proofs}
}

func NewKnowStmt(facts []FactStmt) *KnowStmt {
	return &KnowStmt{facts}
}

func NewAxiomStmt(decl DefPropOrExistPropStmt) *AxiomStmt {
	return &AxiomStmt{decl}
}

func NewThmStmt(decl DefPropOrExistPropStmt, proof []Stmt) *ThmStmt {
	return &ThmStmt{decl, proof}
}

func NewCondFactStmt(condFacts []FactStmt, thenFacts []FactStmt) *CondFactStmt {
	return &CondFactStmt{condFacts, thenFacts}
}

func NewFcFnDecl(name string, params []string) *FcFnDecl {
	return &FcFnDecl{name, params}
}

func NewConDefHeader(name string, params []string, typeParams []Fc) *ConDefHeader {
	return &ConDefHeader{name, params, typeParams}
}

func NewOrAndFact(isOr bool, facts []LogicExprOrSpecFactStmt) *LogicExprStmt {
	return &LogicExprStmt{IsOr: isOr, Facts: facts}
}

func NewExistObjDefStmt(objNames []string, fact SpecFactStmt) *ExistObjDefStmt {
	return &ExistObjDefStmt{objNames, fact}
}

func NewExistPropDef(declHeader ConDefHeader, domFacts []FactStmt, iffFacts []*SpecFactStmt) *ExistPropDef {
	return &ExistPropDef{declHeader, domFacts, iffFacts}
}

func NewDefSetEnumtmt(setName string, elems []Fc) *SetDefEnumtmt {
	return &SetDefEnumtmt{setName, elems}
}

func NewSetDefSetBuilderStmt(setName string, parentSet Fc, facts []FactStmt) *SetDefSetBuilderStmt {
	return &SetDefSetBuilderStmt{setName, parentSet, facts}
}

func NewMatcherEnvStmt(matcherName *FcAtom, params []Fc, body []Stmt) *MatcherEnvStmt {
	return &MatcherEnvStmt{*matcherName, params, body}
}
