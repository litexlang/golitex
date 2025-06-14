// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex discord server: https://discord.gg/uvrHM7eS

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

func NewDefPropStmt(defHeader DefHeader, domFacts []FactStmt, iffFacts []FactStmt) *DefPropStmt {
	return &DefPropStmt{defHeader, domFacts, iffFacts}
}

func NewDefExistPropStmt(def *DefExistPropStmtBody, existParams []string, existParamSets []Fc) *DefExistPropStmt {
	return &DefExistPropStmt{*def, existParams, existParamSets}
}

func NewDefFnStmt(defHeader DefHeader, domFacts []FactStmt, thenFacts []FactStmt, retSet Fc) *DefFnStmt {
	return &DefFnStmt{defHeader, domFacts, thenFacts, retSet}
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

func NewDefHeader(name string, params []string, setParams []Fc) *DefHeader {
	return &DefHeader{name, params, setParams}
}

func NewHaveStmt(objNames []string, fact SpecFactStmt) *HaveStmt {
	return &HaveStmt{objNames, fact}
}

func NewExistPropDef(declHeader DefHeader, domFacts []FactStmt, iffFacts []FactStmt) *DefExistPropStmtBody {
	return &DefExistPropStmtBody{declHeader, domFacts, iffFacts}
}

func NewUniFact(params []string, setParams []Fc, domFacts []FactStmt, thenFacts []FactStmt, iffFacts []FactStmt) *UniFactStmt {
	return &UniFactStmt{params, setParams, domFacts, thenFacts, iffFacts}
}

func NewSetDefSetBuilderStmt(setName string, parentSet Fc, facts []FactStmt) *SetDefSetBuilderStmt {
	return &SetDefSetBuilderStmt{setName, parentSet, facts}
}

func NewProveInEachCaseStmt(orFact OrStmt, thenFacts []FactStmt, proofs [][]Stmt) *ProveInEachCaseStmt {
	return &ProveInEachCaseStmt{orFact, thenFacts, proofs}
}

func NewKnowPropStmt(prop DefPropStmt) *KnowPropStmt {
	return &KnowPropStmt{prop}
}

func NewDefExistPropBodyStmt(defHeader DefHeader, domFacts []FactStmt, iffFacts []FactStmt) *DefExistPropStmtBody {
	return &DefExistPropStmtBody{defHeader, domFacts, iffFacts}
}

func NewFcAtomWithName(name string) *FcAtom {
	return NewFcAtom(glob.EmptyPkg, name)
}

func NewKnowExistPropStmt(existProp DefExistPropStmt) *KnowExistPropStmt {
	return &KnowExistPropStmt{existProp}
}

func NewWhenPropMatchStmt(fact SpecFactStmt, body []Stmt) *SupposeStmt {
	return &SupposeStmt{fact, body}
}

func NewWithPropMatchStmt(fact SpecFactStmt, body []Stmt) *WithPropMatchStmt {
	return &WithPropMatchStmt{fact, body}
}

func NewKnowSupposeStmt(supposeStmt SupposeStmt) *KnowSupposeStmt {
	return &KnowSupposeStmt{supposeStmt}
}

func NewOrStmt(orFacts []SpecFactStmt) *OrStmt {
	return &OrStmt{orFacts}
}

func NewSupposeStmt(fact SpecFactStmt, body []Stmt) *SupposeStmt {
	return &SupposeStmt{fact, body}
}

func NewProveNotForallByExistStmt(fact *UniFactStmt, existObj Fc, proof []Stmt) *ProveNotForallByExistStmt {
	return &ProveNotForallByExistStmt{*fact, existObj, proof}
}
