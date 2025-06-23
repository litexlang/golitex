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
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_ast

import (
	taskManager "golitex/task_manager"
)

func NewPubStmt(stmts []Stmt) *PubStmt {
	return &PubStmt{stmts}
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

func NewFnTemplateStmt(params []string, paramSets []Fc, domFacts []FactStmt, thenFacts []FactStmt, retSet Fc) *FnTemplateStmt {
	return &FnTemplateStmt{params, paramSets, domFacts, thenFacts, retSet}
}

func NewSpecFactStmt(typeEnum SpecFactEnum, propName *FcAtom, params []Fc) *SpecFactStmt {
	return &SpecFactStmt{typeEnum, *propName, params}
}

func NewClaimProveByContradictionStmt(claim ClaimProveStmt) *ClaimProveByContradictionStmt {
	return &ClaimProveByContradictionStmt{claim}
}

func NewClaimStmt(toCheckFact FactStmt, proofs []Stmt) *ClaimProveStmt {
	return &ClaimProveStmt{toCheckFact, proofs}
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

func NewUniFact(params []string, setParams []Fc, domFacts []FactStmt, thenFacts []FactStmt) *UniFactStmt {
	return &UniFactStmt{params, setParams, domFacts, thenFacts}
}

func NewUniFactWithIff(uniFact *UniFactStmt, iffFacts []FactStmt) *UniFactWithIffStmt {
	return &UniFactWithIffStmt{*uniFact, iffFacts}
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
	// return NewFcAtom(glob.EmptyPkg, name)
	return NewFcAtom(taskManager.CurrentPkg, name)
}

func NewKnowExistPropStmt(existProp DefExistPropStmt) *KnowExistPropStmt {
	return &KnowExistPropStmt{existProp}
}

func NewWhenPropMatchStmt(fact SpecFactStmt, body []Stmt) *SupposeStmt {
	return &SupposeStmt{fact, body}
}

func NewWithPropMatchStmt(fact SpecFactStmt, body []Stmt) *WithStmt {
	return &WithStmt{fact, body}
}

func NewOrStmt(orFacts []SpecFactStmt) *OrStmt {
	return &OrStmt{orFacts}
}

func NewSupposeStmt(fact SpecFactStmt, body []Stmt) *SupposeStmt {
	return &SupposeStmt{fact, body}
}

func NewImportStmt(path string, asPkgName string) *ImportStmt {
	return &ImportStmt{path, asPkgName}
}

func NewProveStmt(proof []Stmt) *ProveStmt {
	return &ProveStmt{proof}
}

func NewFnTemplateDefStmt(name string, fnTemplateStmt *FnTemplateStmt) *DefFnTemplateStmt {
	return &DefFnTemplateStmt{name, *fnTemplateStmt}
}

func NewDefFnStmt(name string, fnTemplateStmt *FnTemplateStmt) *DefFnStmt {
	return &DefFnStmt{name, *fnTemplateStmt}
}
