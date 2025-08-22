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

func NewDefObjStmt(objs []string, objSets []Fc, facts []FactStmt) *DefObjStmt {
	return &DefObjStmt{objs, objSets, facts}
}

func NewDefPropStmt(defHeader *DefHeader, domFacts []FactStmt, iffFacts []FactStmt, thenFacts []FactStmt) *DefPropStmt {
	return &DefPropStmt{*defHeader, domFacts, iffFacts, thenFacts}
}

func NewDefExistPropStmt(def *DefExistPropStmtBody, existParams []string, existParamSets []Fc) *DefExistPropStmt {
	return &DefExistPropStmt{*def, existParams, existParamSets}
}

// func NewFnTemplateStmt(defHeader *DefHeader, domFacts []FactStmt, thenFacts []FactStmt, retSet Fc) *FnTemplateStmt {
// 	return &FnTemplateStmt{*defHeader, domFacts, thenFacts, retSet}
// }

func NewSpecFactStmt(typeEnum SpecFactEnum, propName FcAtom, params []Fc) *SpecFactStmt {
	return &SpecFactStmt{typeEnum, propName, params}
}

func NewClaimProveByContradictionStmt(claim ClaimProveStmt) *ClaimProveByContradictionStmt {
	return &ClaimProveByContradictionStmt{claim}
}

func NewClaimProveStmt(toCheckFact FactStmt, proofs []Stmt) *ClaimProveStmt {
	return &ClaimProveStmt{toCheckFact, proofs}
}

func NewKnowStmt(facts CanBeKnownStmtSlice) *KnowFactStmt {
	return &KnowFactStmt{facts}
}

func NewDefHeader(name FcAtom, params []string, setParams []Fc) *DefHeader {
	return &DefHeader{name, params, setParams}
}

func NewHaveStmt(objNames []string, fact SpecFactStmt) *HaveObjStStmt {
	return &HaveObjStStmt{objNames, fact}
}

func NewExistPropDef(declHeader *DefHeader, domFacts []FactStmt, iffFacts []FactStmt) *DefExistPropStmtBody {
	return &DefExistPropStmtBody{*declHeader, domFacts, iffFacts}
}

func NewUniFact(params []string, setParams []Fc, domFacts []FactStmt, thenFacts []FactStmt) *UniFactStmt {
	return &UniFactStmt{params, setParams, domFacts, thenFacts}
}

func NewUniFactWithIff(uniFact *UniFactStmt, iffFacts []FactStmt) *UniFactWithIffStmt {
	return &UniFactWithIffStmt{*uniFact, iffFacts}
}

func NewProveInEachCaseStmt(orFact OrStmt, thenFacts []FactStmt, proofs []StmtSlice) *ProveInEachCaseStmt {
	return &ProveInEachCaseStmt{orFact, thenFacts, proofs}
}

func NewKnowPropStmt(prop DefPropStmt) *KnowPropStmt {
	return &KnowPropStmt{prop}
}

func NewDefExistPropBodyStmt(defHeader *DefHeader, domFacts []FactStmt, iffFacts []FactStmt) *DefExistPropStmtBody {
	return &DefExistPropStmtBody{*defHeader, domFacts, iffFacts}
}

func NewOrStmt(orFacts []*SpecFactStmt) *OrStmt {
	return &OrStmt{orFacts}
}

func NewImportStmt(path string, asPkgName string) *ImportDirStmt {
	return &ImportDirStmt{path, asPkgName}
}

func NewProveStmt(proof []Stmt) *ProveStmt {
	return &ProveStmt{proof}
}

func NewDefFnStmt(name string, fnTemplate *FnTStruct) *DefFnStmt {
	return &DefFnStmt{name, *fnTemplate}
}

func NewEnumStmt(enumName Fc, enumValues []Fc) *EnumStmt {
	return &EnumStmt{enumName, enumValues}
}

func NewImportFileStmt(path string) *ImportFileStmt {
	return &ImportFileStmt{path}
}

func NewClaimPropStmt(prop *DefPropStmt, proofs []Stmt, isProve bool) *ClaimPropStmt {
	return &ClaimPropStmt{*prop, proofs, isProve}
}

func NewClaimExistPropStmt(existProp *DefExistPropStmt, proofs []Stmt) *ClaimExistPropStmt {
	return &ClaimExistPropStmt{*existProp, proofs}
}

// func NewProveByMathInductionStmt(fact *SpecFactStmt, paramIndex int, start int) *ProveByMathInductionStmt {
// 	return &ProveByMathInductionStmt{fact, paramIndex, start}
// }

func NewIntensionalSetStmt(curSet Fc, param string, parentSet Fc, proofs []*SpecFactStmt) *IntensionalSetStmt {
	return &IntensionalSetStmt{curSet, param, parentSet, proofs}
}

func NewProveOverFiniteSetStmt(fact *UniFactStmt, proofs []Stmt) *ProveOverFiniteSetStmt {
	return &ProveOverFiniteSetStmt{*fact, proofs}
}

func NewHaveObjInNonEmptySetStmt(objNames []string, objSets []Fc) *HaveObjInNonEmptySetStmt {
	return &HaveObjInNonEmptySetStmt{objNames, objSets}
}

func NewHaveSetStmt(fact EnumSet_IntensionalSet_EqualDom) *HaveSetStmt {
	return &HaveSetStmt{fact}
}

func NewHaveSetFnStmt(declHeader *DefHeader, param string, parentSet Fc, proofs []*SpecFactStmt) *HaveSetFnStmt {
	return &HaveSetFnStmt{*declHeader, param, parentSet, proofs}
}

func NewHaveSetDefinedByReplacementStmt(name string, domSet Fc, rangeSet Fc, propName FcAtom) *HaveSetDefinedByReplacementStmt {
	return &HaveSetDefinedByReplacementStmt{name, domSet, rangeSet, propName}
}

func NewNamedUniFactStmt(defPropStmt *DefPropStmt) *NamedUniFactStmt {
	return &NamedUniFactStmt{*defPropStmt}
}

func NewEqualsFactStmt(params FcSlice) *EqualsFactStmt {
	return &EqualsFactStmt{params}
}

func NewKnowExistPropStmt(existProp DefExistPropStmt) *KnowExistPropStmt {
	return &KnowExistPropStmt{existProp}
}

func NewCommentStmt(comment string) *CommentStmt {
	return &CommentStmt{comment}
}

func NewFnTemplateStmt(defHeader *DefHeader, templateDomFacts []FactStmt, fnParams []string, fnParamSets []Fc, fnRetSet Fc, fnDomFacts []FactStmt, fnThenFacts []FactStmt) *FnTemplateDefStmt {
	return &FnTemplateDefStmt{*defHeader, templateDomFacts, *NewFnTStruct(fnParams, fnParamSets, fnRetSet, fnDomFacts, fnThenFacts)}
}

func NewFnTStruct(params []string, paramSets []Fc, retSet Fc, domFacts []FactStmt, thenFacts []FactStmt) *FnTStruct {
	return &FnTStruct{params, paramSets, retSet, domFacts, thenFacts}
}

func NewClearStmt() *ClearStmt {
	return &ClearStmt{}
}

func NewInlineFactsStmt(facts []FactStmt) *InlineFactsStmt {
	return &InlineFactsStmt{facts}
}

func NewProveByInductionStmt(fact *SpecFactStmt, param string, start Fc) *ProveByInductionStmt {
	return &ProveByInductionStmt{fact, param, start}
}

func NewHaveObjEqualStmt(objNames []string, objEqualTos []Fc, objSets []Fc) *HaveObjEqualStmt {
	return &HaveObjEqualStmt{objNames, objEqualTos, objSets}
}

func NewHaveFnEqualStmt(defHeader *DefHeader, equalTo Fc, domFacts []FactStmt) *HaveFnEqualStmt {
	return &HaveFnEqualStmt{*defHeader, equalTo, domFacts}
}

func NewHaveFnLiftStmt(fnName string, opt Fc, domainOfEachParamOfGivenFn []Fc) *HaveFnLiftStmt {
	return &HaveFnLiftStmt{fnName, opt, domainOfEachParamOfGivenFn}
}
