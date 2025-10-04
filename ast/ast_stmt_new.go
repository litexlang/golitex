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

func NewDefObjStmt(objs []string, objSets []Fc, facts []FactStmt, line uint) *DefObjStmt {
	return &DefObjStmt{objs, objSets, facts, line}
}

func NewDefPropStmt(defHeader *DefHeader, domFacts []FactStmt, iffFacts []FactStmt, thenFacts []FactStmt, line uint) *DefPropStmt {
	return &DefPropStmt{*defHeader, domFacts, iffFacts, thenFacts, line}
}

func NewDefExistPropStmt(def *DefExistPropStmtBody, existParams []string, existParamSets []Fc, line uint) *DefExistPropStmt {
	return &DefExistPropStmt{*def, existParams, existParamSets, line}
}

func NewSpecFactStmt(typeEnum SpecFactEnum, propName FcAtom, params []Fc, line uint) *SpecFactStmt {
	return &SpecFactStmt{typeEnum, propName, params, line}
}

func NewClaimProveByContradictionStmt(claim ClaimProveStmt, line uint) *ClaimProveByContradictionStmt {
	return &ClaimProveByContradictionStmt{claim, line}
}

func NewClaimProveStmt(toCheckFact FactStmt, proofs []Stmt, line uint) *ClaimProveStmt {
	return &ClaimProveStmt{toCheckFact, proofs, line}
}

func NewKnowStmt(facts CanBeKnownStmtSlice, line uint) *KnowFactStmt {
	return &KnowFactStmt{facts, line}
}

func NewDefHeader(name FcAtom, params []string, setParams []Fc) *DefHeader {
	return &DefHeader{name, params, setParams}
}

func NewHaveStmt(objNames []string, fact SpecFactStmt, line uint) *HaveObjStStmt {
	return &HaveObjStStmt{objNames, fact, line}
}

func NewExistPropDef(declHeader *DefHeader, domFacts []FactStmt, iffFacts []FactStmt, thenFacts []FactStmt, line uint) *DefExistPropStmtBody {
	return &DefExistPropStmtBody{*declHeader, domFacts, iffFacts, thenFacts, line}
}

func NewUniFact(params []string, setParams []Fc, domFacts []FactStmt, thenFacts []FactStmt, line uint) *UniFactStmt {
	return &UniFactStmt{params, setParams, domFacts, thenFacts, line}
}

func NewUniFactWithIff(uniFact *UniFactStmt, iffFacts []FactStmt, line uint) *UniFactWithIffStmt {
	return &UniFactWithIffStmt{*uniFact, iffFacts, line}
}

func NewProveInEachCaseStmt(orFact OrStmt, thenFacts []FactStmt, proofs []StmtSlice, line uint) *ProveInEachCaseStmt {
	return &ProveInEachCaseStmt{orFact, thenFacts, proofs, line}
}

func NewKnowPropStmt(prop DefPropStmt, line uint) *KnowPropStmt {
	return &KnowPropStmt{prop, line}
}

func NewDefExistPropBodyStmt(defHeader *DefHeader, domFacts []FactStmt, iffFacts []FactStmt, thenFacts []FactStmt, line uint) *DefExistPropStmtBody {
	return &DefExistPropStmtBody{*defHeader, domFacts, iffFacts, thenFacts, line}
}

func NewOrStmt(orFacts []*SpecFactStmt, line uint) *OrStmt {
	return &OrStmt{orFacts, line}
}

func NewImportStmt(path string, asPkgName string, line uint) *ImportDirStmt {
	return &ImportDirStmt{path, asPkgName, line}
}

func NewProveStmt(proof []Stmt, line uint) *ProveStmt {
	return &ProveStmt{proof, line}
}

func NewDefFnStmt(name string, fnTemplate *FnTStruct, line uint) *DefFnStmt {
	return &DefFnStmt{name, *fnTemplate, line}
}

func NewEnumStmt(enumName Fc, enumValues []Fc, line uint) *EnumStmt {
	return &EnumStmt{enumName, enumValues, line}
}

func NewImportFileStmt(path string, line uint) *ImportFileStmt {
	return &ImportFileStmt{path, line}
}

func NewClaimPropStmt(prop *DefPropStmt, proofs []Stmt, isProve bool, line uint) *ClaimPropStmt {
	return &ClaimPropStmt{*prop, proofs, isProve, line}
}

func NewClaimExistPropStmt(existProp *DefExistPropStmt, proofs []Stmt, haveObj []Fc, line uint) *ClaimExistPropStmt {
	return &ClaimExistPropStmt{*existProp, proofs, haveObj, line}
}

func NewIntensionalSetStmt(curSet Fc, param string, parentSet Fc, proofs []*SpecFactStmt, line uint) *IntensionalSetStmt {
	return &IntensionalSetStmt{curSet, param, parentSet, proofs, line}
}

func NewProveOverFiniteSetStmt(fact *UniFactStmt, proofs []StmtSlice, line uint) *ProveOverFiniteSetStmt {
	return &ProveOverFiniteSetStmt{*fact, proofs, line}
}

func NewHaveObjInNonEmptySetStmt(objNames []string, objSets []Fc, line uint) *HaveObjInNonEmptySetStmt {
	return &HaveObjInNonEmptySetStmt{objNames, objSets, line}
}

func NewHaveSetStmt(fact EnumSet_IntensionalSet_EqualDom, line uint) *HaveSetStmt {
	return &HaveSetStmt{fact, line}
}

func NewHaveSetFnStmt(declHeader *DefHeader, param string, parentSet Fc, proofs []*SpecFactStmt, line uint) *HaveSetFnStmt {
	return &HaveSetFnStmt{*declHeader, param, parentSet, proofs, line}
}

func NewHaveSetDefinedByReplacementStmt(name string, domSet Fc, rangeSet Fc, propName FcAtom, line uint) *HaveSetDefinedByReplacementStmt {
	return &HaveSetDefinedByReplacementStmt{name, domSet, rangeSet, propName, line}
}

func NewNamedUniFactStmt(defPropStmt *DefPropStmt, line uint) *NamedUniFactStmt {
	return &NamedUniFactStmt{*defPropStmt, line}
}

func NewEqualsFactStmt(params FcSlice, line uint) *EqualsFactStmt {
	return &EqualsFactStmt{params, line}
}

func NewKnowExistPropStmt(existProp *DefExistPropStmt, line uint) *KnowExistPropStmt {
	return &KnowExistPropStmt{*existProp, line}
}

func NewLatexStmt(comment string, line uint) *LatexStmt {
	return &LatexStmt{comment, line}
}

func NewFnTemplateStmt(defHeader *DefHeader, templateDomFacts []FactStmt, fnTStruct *FnTStruct, line uint) *FnTemplateDefStmt {
	return &FnTemplateDefStmt{*defHeader, templateDomFacts, *fnTStruct, line}
}

func NewFnTStruct(params []string, paramSets []Fc, retSet Fc, domFacts []FactStmt, thenFacts []FactStmt, line uint) *FnTStruct {
	return &FnTStruct{params, paramSets, retSet, domFacts, thenFacts, line}
}

func NewClearStmt(line uint) *ClearStmt {
	return &ClearStmt{line}
}

func NewInlineFactsStmt(facts []FactStmt, line uint) *InlineFactsStmt {
	return &InlineFactsStmt{facts, line}
}

func NewProveByInductionStmt(fact *SpecFactStmt, param string, start Fc, line uint) *ProveByInductionStmt {
	return &ProveByInductionStmt{fact, param, start, line}
}

func NewHaveObjEqualStmt(objNames []string, objEqualTos []Fc, objSets []Fc, line uint) *HaveObjEqualStmt {
	return &HaveObjEqualStmt{objNames, objEqualTos, objSets, line}
}

func NewHaveFnEqualStmt(defHeader *DefHeader, retSet Fc, equalTo Fc, line uint) *HaveFnEqualStmt {
	return &HaveFnEqualStmt{*defHeader, retSet, equalTo, line}
}

func NewHaveFnLiftStmt(fnName string, opt Fc, domainOfEachParamOfGivenFn []Fc, line uint) *HaveFnLiftStmt {
	return &HaveFnLiftStmt{fnName, opt, domainOfEachParamOfGivenFn, line}
}

func NewClaimHaveFnStmt(defFnStmt *DefFnStmt, proof []Stmt, haveObjSatisfyFn Fc, line uint) *HaveFnStmt {
	return &HaveFnStmt{*defFnStmt, proof, haveObjSatisfyFn, line}
}

func NewMarkdownStmt(comment string, line uint) *MarkdownStmt {
	return &MarkdownStmt{comment, line}
}

func NewProveInRangeStmt(start int64, end int64, param string, domFacts []FactStmt, thenFacts []FactStmt, proofs []Stmt, line uint) *ProveInRangeStmt {
	return &ProveInRangeStmt{start, end, param, domFacts, thenFacts, proofs, line}
}
