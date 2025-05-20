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

import (
	glob "golitex/glob"
)

func NewTopStmt(stmt Stmt, isPub bool) *TopStmt {
	return &TopStmt{stmt, isPub}
}

func NewDefObjStmt(objs []string, facts []FactStmt, objInSetsFacts []FactStmt) *DefObjStmt {
	return &DefObjStmt{objs, facts, objInSetsFacts}
}

func NewDefPropStmt(defHeader DefHeader, domFacts []FactStmt, iffFacts []FactStmt) *DefPropStmt {
	return &DefPropStmt{defHeader, domFacts, iffFacts}
}

func NewDefExistPropStmt(def *DefExistPropStmtBody, existParams []string, existInSetsFacts []FactStmt) *DefExistPropStmt {
	return &DefExistPropStmt{*def, existParams, existInSetsFacts}
}

func NewDefFnStmt(defHeader DefHeader, domFacts []FactStmt, thenFacts []FactStmt, retInSetsFacts FactStmt) *DefFnStmt {
	return &DefFnStmt{defHeader, domFacts, thenFacts, retInSetsFacts}
}

func newUniFactStmt(params []string, domFacts []FactStmt, thenFacts []FactStmt, iffFacts []FactStmt, paramInSetsFacts []FactStmt) *UniFactStmt {
	return &UniFactStmt{params, domFacts, thenFacts, iffFacts, paramInSetsFacts}
}

func NewSpecFactStmt(typeEnum SpecFactEnum, propName FcAtom, params []Fc) *SpecFactStmt {
	return &SpecFactStmt{typeEnum, propName, params}
}

func NewClaimProveStmt(proveTrue bool, toCheckFact FactStmt, proofs []Stmt) *ClaimStmt {
	return &ClaimStmt{proveTrue, toCheckFact, proofs}
}

func NewKnowStmt(facts []FactStmt) *KnowFactStmt {
	return &KnowFactStmt{facts}
}

func NewFcFnDecl(name string, params []string) *FcFnDecl {
	return &FcFnDecl{name, params}
}

func NewDefHeader(name string, params []string, paramInSetsFacts []FactStmt) *DefHeader {
	return &DefHeader{name, params, paramInSetsFacts}
}

func NewOrAndFact(isOr bool, facts []Reversable_LogicOrSpec_Stmt) *LogicExprStmt {
	return &LogicExprStmt{IsOr: isOr, Facts: facts}
}

func NewHaveStmt(objNames []string, fact SpecFactStmt) *HaveStmt {
	return &HaveStmt{objNames, fact}
}

func NewExistPropDef(declHeader DefHeader, domFacts []FactStmt, iffFacts []Reversable_LogicOrSpec_Stmt) *DefExistPropStmtBody {
	return &DefExistPropStmtBody{declHeader, domFacts, iffFacts}
}

// func NewDefSetEnumtmt(setName string, elems []Fc) *SetDefEnumtmt {
// 	return &SetDefEnumtmt{setName, elems}
// }

// func NewSetDefSetBuilderStmt(setName string, parentSet Fc, facts []FactStmt) *SetDefSetBuilderStmt {
// 	return &SetDefSetBuilderStmt{setName, parentSet, facts}
// }

func NewUniFactStmtWithSetReqInDom(params []string, domFacts []FactStmt, thenFacts []FactStmt, iffFacts []FactStmt, paramInSetsFacts []FactStmt) *UniFactStmt {
	return newUniFactStmt(params, domFacts, thenFacts, iffFacts, paramInSetsFacts)
}

func NewSetDefSetBuilderStmt(setName string, parentSet Fc, facts []FactStmt) *SetDefSetBuilderStmt {
	return &SetDefSetBuilderStmt{setName, parentSet, facts}
}

func NewProveInEachCaseStmt(orFact LogicExprStmt, thenFacts []FactStmt, proofs [][]Stmt) *ProveInEachCaseStmt {
	return &ProveInEachCaseStmt{orFact, thenFacts, proofs}
}

func NewKnowPropStmt(prop DefPropStmt) *KnowPropStmt {
	return &KnowPropStmt{prop}
}

func NewDefExistPropBodyStmt(defHeader DefHeader, domFacts []FactStmt, iffFacts []Reversable_LogicOrSpec_Stmt) *DefExistPropStmtBody {
	return &DefExistPropStmtBody{defHeader, domFacts, iffFacts}
}

func NewFcAtomWithName(name string) *FcAtom {
	return NewFcAtom(glob.EmptyPkg, name)
}

func NewProveOrStmt(indexes map[int]struct{}, orFact LogicExprStmt, proofs []Stmt) *ProveOrStmt {
	return &ProveOrStmt{indexes, orFact, proofs}
}

func NewKnowExistPropStmt(existProp DefExistPropStmt) *KnowExistPropStmt {
	return &KnowExistPropStmt{existProp}
}

func NewWhenPropMatchStmt(fact SpecFactStmt, body []FactStmt) *SupposePropMatchStmt {
	return &SupposePropMatchStmt{fact, body}
}

func NewWithPropMatchStmt(fact SpecFactStmt, body []FactStmt) *WithPropMatchStmt {
	return &WithPropMatchStmt{fact, body}
}
