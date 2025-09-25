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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_ast

func NewDefObjStmt(objs []string, objSets []Fc, facts []FactStmt) *DefObjStmt {
	return &DefObjStmt{objs, objSets, facts, 0}
}

func NewDefPropStmt(defHeader *DefHeader, domFacts []FactStmt, iffFacts []FactStmt, thenFacts []FactStmt) *DefPropStmt {
	return &DefPropStmt{*defHeader, domFacts, iffFacts, thenFacts, 0}
}

func NewDefExistPropStmt(def *DefExistPropStmtBody, existParams []string, existParamSets []Fc) *DefExistPropStmt {
	return &DefExistPropStmt{*def, existParams, existParamSets, 0}
}

// func NewFnTemplateStmt(defHeader *DefHeader, domFacts []FactStmt, thenFacts []FactStmt, retSet Fc) *FnTemplateStmt {
// 	return &FnTemplateStmt{*defHeader, domFacts, thenFacts, retSet}
// }

func NewSpecFactStmt(typeEnum SpecFactEnum, propName FcAtom, params []Fc) *SpecFactStmt {
	return &SpecFactStmt{typeEnum, propName, params, 0}
}

func NewClaimProveByContradictionStmt(claim ClaimProveStmt) *ClaimProveByContradictionStmt {
	return &ClaimProveByContradictionStmt{claim, 0}
}

func NewClaimProveStmt(toCheckFact FactStmt, proofs []Stmt) *ClaimProveStmt {
	return &ClaimProveStmt{toCheckFact, proofs, 0}
}

func NewKnowStmt(facts CanBeKnownStmtSlice) *KnowFactStmt {
	return &KnowFactStmt{facts, 0}
}

func NewDefHeader(name FcAtom, params []string, setParams []Fc) *DefHeader {
	return &DefHeader{name, params, setParams, 0}
}

func NewHaveStmt(objNames []string, fact SpecFactStmt) *HaveObjStStmt {
	return &HaveObjStStmt{objNames, fact, 0}
}

func NewExistPropDef(declHeader *DefHeader, domFacts []FactStmt, iffFacts []FactStmt) *DefExistPropStmtBody {
	return &DefExistPropStmtBody{*declHeader, domFacts, iffFacts, 0}
}

func NewUniFact(params []string, setParams []Fc, domFacts []FactStmt, thenFacts []FactStmt) *UniFactStmt {
	return &UniFactStmt{params, setParams, domFacts, thenFacts, 0}
}

func NewUniFactWithIff(uniFact *UniFactStmt, iffFacts []FactStmt) *UniFactWithIffStmt {
	return &UniFactWithIffStmt{*uniFact, iffFacts, 0}
}

func NewProveInEachCaseStmt(orFact OrStmt, thenFacts []FactStmt, proofs []StmtSlice) *ProveInEachCaseStmt {
	return &ProveInEachCaseStmt{orFact, thenFacts, proofs, 0}
}

func NewKnowPropStmt(prop DefPropStmt) *KnowPropStmt {
	return &KnowPropStmt{prop, 0}
}

func NewDefExistPropBodyStmt(defHeader *DefHeader, domFacts []FactStmt, iffFacts []FactStmt) *DefExistPropStmtBody {
	return &DefExistPropStmtBody{*defHeader, domFacts, iffFacts, 0}
}

func NewOrStmt(orFacts []*SpecFactStmt) *OrStmt {
	return &OrStmt{orFacts, 0}
}

func NewImportStmt(path string, asPkgName string) *ImportDirStmt {
	return &ImportDirStmt{path, asPkgName, 0}
}

func NewProveStmt(proof []Stmt) *ProveStmt {
	return &ProveStmt{proof, 0}
}

func NewDefFnStmt(name string, fnTemplate *FnTStruct) *DefFnStmt {
	return &DefFnStmt{name, *fnTemplate, 0}
}

func NewEnumStmt(enumName Fc, enumValues []Fc) *EnumStmt {
	return &EnumStmt{enumName, enumValues, 0}
}

func NewImportFileStmt(path string) *ImportFileStmt {
	return &ImportFileStmt{path, 0}
}

func NewClaimPropStmt(prop *DefPropStmt, proofs []Stmt, isProve bool) *ClaimPropStmt {
	return &ClaimPropStmt{*prop, proofs, isProve, 0}
}

func NewClaimExistPropStmt(existProp *DefExistPropStmt, proofs []Stmt) *ClaimExistPropStmt {
	return &ClaimExistPropStmt{*existProp, proofs, 0}
}

// func NewProveByMathInductionStmt(fact *SpecFactStmt, paramIndex int, start int) *ProveByMathInductionStmt {
// 	return &ProveByMathInductionStmt{fact, paramIndex, start}
// }

func NewIntensionalSetStmt(curSet Fc, param string, parentSet Fc, proofs []*SpecFactStmt) *IntensionalSetStmt {
	return &IntensionalSetStmt{curSet, param, parentSet, proofs, 0}
}

func NewProveOverFiniteSetStmt(fact *UniFactStmt, proofs []StmtSlice) *ProveOverFiniteSetStmt {
	return &ProveOverFiniteSetStmt{*fact, proofs, 0}
}

func NewHaveObjInNonEmptySetStmt(objNames []string, objSets []Fc) *HaveObjInNonEmptySetStmt {
	return &HaveObjInNonEmptySetStmt{objNames, objSets, 0}
}

func NewHaveSetStmt(fact EnumSet_IntensionalSet_EqualDom) *HaveSetStmt {
	return &HaveSetStmt{fact, 0}
}

func NewHaveSetFnStmt(declHeader *DefHeader, param string, parentSet Fc, proofs []*SpecFactStmt) *HaveSetFnStmt {
	return &HaveSetFnStmt{*declHeader, param, parentSet, proofs, 0}
}

func NewHaveSetDefinedByReplacementStmt(name string, domSet Fc, rangeSet Fc, propName FcAtom) *HaveSetDefinedByReplacementStmt {
	return &HaveSetDefinedByReplacementStmt{name, domSet, rangeSet, propName, 0}
}

func NewNamedUniFactStmt(defPropStmt *DefPropStmt) *NamedUniFactStmt {
	return &NamedUniFactStmt{*defPropStmt, 0}
}

func NewEqualsFactStmt(params FcSlice) *EqualsFactStmt {
	return &EqualsFactStmt{params, 0}
}

func NewKnowExistPropStmt(existProp DefExistPropStmt) *KnowExistPropStmt {
	return &KnowExistPropStmt{existProp, 0}
}

func NewCommentStmt(comment string) *CommentStmt {
	return &CommentStmt{comment, 0}
}

func NewFnTemplateStmt(defHeader *DefHeader, templateDomFacts []FactStmt, fnParams []string, fnParamSets []Fc, fnRetSet Fc, fnDomFacts []FactStmt, fnThenFacts []FactStmt) *FnTemplateDefStmt {
	return &FnTemplateDefStmt{*defHeader, templateDomFacts, *NewFnTStruct(fnParams, fnParamSets, fnRetSet, fnDomFacts, fnThenFacts), 0}
}

func NewFnTStruct(params []string, paramSets []Fc, retSet Fc, domFacts []FactStmt, thenFacts []FactStmt) *FnTStruct {
	return &FnTStruct{params, paramSets, retSet, domFacts, thenFacts, 0}
}

func NewClearStmt() *ClearStmt {
	return &ClearStmt{0}
}

func NewInlineFactsStmt(facts []FactStmt) *InlineFactsStmt {
	return &InlineFactsStmt{facts, 0}
}

func NewProveByInductionStmt(fact *SpecFactStmt, param string, start Fc) *ProveByInductionStmt {
	return &ProveByInductionStmt{fact, param, start, 0}
}

func NewHaveObjEqualStmt(objNames []string, objEqualTos []Fc, objSets []Fc) *HaveObjEqualStmt {
	return &HaveObjEqualStmt{objNames, objEqualTos, objSets, 0}
}

func NewHaveFnEqualStmt(defHeader *DefHeader, retSet Fc, equalTo Fc) *HaveFnEqualStmt {
	return &HaveFnEqualStmt{*defHeader, retSet, equalTo, 0}
}

func NewHaveFnLiftStmt(fnName string, opt Fc, domainOfEachParamOfGivenFn []Fc) *HaveFnLiftStmt {
	return &HaveFnLiftStmt{fnName, opt, domainOfEachParamOfGivenFn, 0}
}

func NewClaimHaveFnStmt(defFnStmt *DefFnStmt, proof []Stmt, haveObjSatisfyFn Fc) *HaveFnStmt {
	return &HaveFnStmt{*defFnStmt, proof, haveObjSatisfyFn, 0}
}
