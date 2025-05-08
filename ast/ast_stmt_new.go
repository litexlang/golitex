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

func NewDefObjStmt(objs []string, objSets []Fc, facts []FactStmt) *DefObjStmt {
	return &DefObjStmt{objs, objSets, facts}
}

func NewDefPropStmt(defHeader DefHeader, domFacts []FactStmt, iffFacts []FactStmt, isCommutative bool) *DefPropStmt {
	return &DefPropStmt{defHeader, domFacts, iffFacts, isCommutative}
}

func NewDefExistPropStmt(def *ExistPropDef, existParams []string, existParamSets []Fc) *DefExistPropStmt {
	return &DefExistPropStmt{*def, existParams, existParamSets}
}

func NewDefFnStmt(defHeader DefHeader, retType Fc, domFacts []FactStmt, thenFacts []FactStmt) *DefFnStmt {
	return &DefFnStmt{defHeader, retType, domFacts, thenFacts}
}

func newUniFactStmt(params []string, paramTypes []Fc, domFacts []FactStmt, thenFacts []FactStmt, iffFacts []FactStmt) *UniFactStmt {
	return &UniFactStmt{params, paramTypes, domFacts, thenFacts, iffFacts}
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

func NewFcFnDecl(name string, params []string) *FcFnDecl {
	return &FcFnDecl{name, params}
}

func NewDefHeader(name string, params []string, typeParams []Fc) *DefHeader {
	return &DefHeader{name, params, typeParams}
}

func NewOrAndFact(isOr bool, facts []Reversable_LogicOrSpec_Stmt) *LogicExprStmt {
	return &LogicExprStmt{IsOr: isOr, Facts: facts}
}

func NewHaveStmt(objNames []string, fact SpecFactStmt) *HaveStmt {
	return &HaveStmt{objNames, fact}
}

func NewExistPropDef(declHeader DefHeader, domFacts []FactStmt, iffFacts []Reversable_LogicOrSpec_Stmt) *ExistPropDef {
	return &ExistPropDef{declHeader, domFacts, iffFacts}
}

// func NewDefSetEnumtmt(setName string, elems []Fc) *SetDefEnumtmt {
// 	return &SetDefEnumtmt{setName, elems}
// }

// func NewSetDefSetBuilderStmt(setName string, parentSet Fc, facts []FactStmt) *SetDefSetBuilderStmt {
// 	return &SetDefSetBuilderStmt{setName, parentSet, facts}
// }

func NewMatcherEnvStmt(matcherName *FcAtom, params []Fc, body []Stmt) *MatcherEnvStmt {
	return &MatcherEnvStmt{*matcherName, params, body}
}

func NewUniFactStmtWithSetReqInDom(params []string, paramTypes []Fc, domFacts []FactStmt, thenFacts []FactStmt, iffFacts []FactStmt) *UniFactStmt {
	if glob.VerifyFcSatisfySpecFactParaReq {
		newDomFacts := []FactStmt{}
		for i, param := range params {
			atom := NewFcAtom(glob.BtEmptyPkgName, param)
			var inFc = NewFcAtom(glob.BtEmptyPkgName, glob.KeywordIn)
			specFact := NewSpecFactStmt(TrueAtom, *inFc, []Fc{atom, paramTypes[i]})
			newDomFacts = append(newDomFacts, specFact)
		}
		newDomFacts = append(newDomFacts, domFacts...)
		newUniFact := newUniFactStmt(params, paramTypes, newDomFacts, thenFacts, iffFacts)
		return newUniFact
	}
	return newUniFactStmt(params, paramTypes, domFacts, thenFacts, iffFacts)
}

func NewSetDefSetBuilderStmt(setName string, parentSet Fc, facts []FactStmt, elems []Fc) *SetDefSetBuilderStmt {
	return &SetDefSetBuilderStmt{setName, parentSet, facts, elems}
}

func NewProveInEachCaseStmt(orFact LogicExprStmt, thenFacts []FactStmt, proofs [][]Stmt) *ProveInEachCaseStmt {
	return &ProveInEachCaseStmt{orFact, thenFacts, proofs}
}

func NewKnowPropStmt(prop DefPropStmt) *KnowPropStmt {
	return &KnowPropStmt{prop}
}
