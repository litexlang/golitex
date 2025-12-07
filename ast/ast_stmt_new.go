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

import (
	"fmt"
	glob "golitex/glob"
	"slices"
)

func NewDefLetStmt(objs []string, objSets []Obj, facts []FactStmt, line uint) *DefLetStmt {
	return &DefLetStmt{objs, objSets, facts, line}
}

func NewDefPropStmt(defHeader *DefHeader, domFacts []FactStmt, iffFacts []FactStmt, thenFacts []FactStmt, line uint) *DefPropStmt {
	return &DefPropStmt{defHeader, domFacts, iffFacts, thenFacts, line}
}

func NewDefExistPropStmt(def *DefExistPropStmtBody, existParams []string, existParamSets []Obj, line uint) *DefExistPropStmt {
	return &DefExistPropStmt{def, existParams, existParamSets, line}
}

func NewSpecFactStmt(typeEnum SpecFactEnum, propName Atom, params []Obj, line uint) *SpecFactStmt {
	return &SpecFactStmt{typeEnum, propName, params, line}
}

func NewClaimProveByContradictionStmt(claim *ClaimProveStmt, line uint) *ClaimProveByContradictionStmt {
	return &ClaimProveByContradictionStmt{claim, line}
}

func NewClaimProveStmt(toCheckFact FactStmt, proofs []Stmt, line uint) *ClaimProveStmt {
	return &ClaimProveStmt{toCheckFact, proofs, line}
}

func NewKnowStmt(facts CanBeKnownStmtSlice, line uint) *KnowFactStmt {
	return &KnowFactStmt{facts, line}
}

func NewDefHeader(name Atom, params []string, setParams []Obj) *DefHeader {
	return &DefHeader{name, params, setParams}
}

func NewHaveStmt(objNames []string, fact *SpecFactStmt, line uint) *HaveObjStStmt {
	return &HaveObjStStmt{objNames, fact, line}
}

func NewExistPropDef(declHeader *DefHeader, domFacts []FactStmt, iffFacts []FactStmt, thenFacts []FactStmt, line uint) *DefExistPropStmtBody {
	return &DefExistPropStmtBody{declHeader, domFacts, iffFacts, thenFacts, line}
}

func NewUniFact(params []string, setParams []Obj, domFacts []FactStmt, thenFacts []FactStmt, line uint) *UniFactStmt {
	return &UniFactStmt{params, setParams, domFacts, thenFacts, line}
}

func NewUniFactWithIff(uniFact *UniFactStmt, iffFacts []FactStmt, line uint) *UniFactWithIffStmt {
	return &UniFactWithIffStmt{uniFact, iffFacts, line}
}

func NewProveInEachCaseStmt(orFact *OrStmt, thenFacts []FactStmt, proofs StmtSliceSlice, line uint) *ProveInEachCaseStmt {
	return &ProveInEachCaseStmt{orFact, thenFacts, proofs, line}
}

func NewProveCaseByCaseStmt(caseFacts []*SpecFactStmt, thenFacts []FactStmt, proofs StmtSliceSlice, line uint) *ProveCaseByCaseStmt {
	return &ProveCaseByCaseStmt{caseFacts, thenFacts, proofs, line}
}

func NewKnowPropStmt(prop *DefPropStmt, line uint) *KnowPropStmt {
	return &KnowPropStmt{prop, line}
}

func NewDefExistPropBodyStmt(defHeader *DefHeader, domFacts []FactStmt, iffFacts []FactStmt, thenFacts []FactStmt, line uint) *DefExistPropStmtBody {
	return &DefExistPropStmtBody{defHeader, domFacts, iffFacts, thenFacts, line}
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
	return &DefFnStmt{name, fnTemplate, line}
}

// func NewEnumStmt(enumName Obj, enumValues []Obj, line uint) *EnumStmt {
// 	return &EnumStmt{enumName, enumValues, line}
// }

func NewImportFileStmt(path string, line uint) *ImportFileStmt {
	return &ImportFileStmt{path, line}
}

func NewClaimPropStmt(prop *DefPropStmt, proofs []Stmt, line uint) *ClaimPropStmt {
	return &ClaimPropStmt{prop, proofs, line}
}

func NewClaimExistPropStmt(existProp *DefExistPropStmt, proofs []Stmt, haveObj []Obj, line uint) *ClaimExistPropStmt {
	return &ClaimExistPropStmt{existProp, proofs, haveObj, line}
}

// func NewIntensionalSetStmt(curSet Obj, param string, parentSet Obj, proofs []*SpecFactStmt, line uint) *IntensionalSetStmt {
// 	return &IntensionalSetStmt{curSet, param, parentSet, proofs, line}
// }

func NewProveByEnumStmt(fact *UniFactStmt, proofs []Stmt, line uint) *ProveByEnumStmt {
	return &ProveByEnumStmt{fact, proofs, line}
}

func NewHaveObjInNonEmptySetStmt(objNames []string, objSets []Obj, line uint) *HaveObjInNonEmptySetStmt {
	return &HaveObjInNonEmptySetStmt{objNames, objSets, line}
}

func NewHaveEnumSetStmt(name string, enumSetObj *FnObj, line uint) *HaveEnumSetStmt {
	return &HaveEnumSetStmt{name, enumSetObj, line}
}

func NewHaveIntensionalSetStmt(param string, parentSet Obj, facts FactStmtSlice, line uint) *HaveIntensionalSetStmt {
	return &HaveIntensionalSetStmt{param, parentSet, facts, line}
}

func NewHaveSetFnStmt(declHeader *DefHeader, param string, parentSet Obj, proofs []*SpecFactStmt, line uint) *HaveSetFnStmt {
	return &HaveSetFnStmt{declHeader, param, parentSet, proofs, line}
}

func NewHaveSetDefinedByReplacementStmt(name string, domSet Obj, rangeSet Obj, propName Atom, line uint) *HaveSetDefinedByReplacementStmt {
	return &HaveSetDefinedByReplacementStmt{name, domSet, rangeSet, propName, line}
}

func NewNamedUniFactStmt(defPropStmt *DefPropStmt, line uint) *NamedUniFactStmt {
	return &NamedUniFactStmt{defPropStmt, line}
}

func NewEqualsFactStmt(params ObjSlice, line uint) *EqualsFactStmt {
	return &EqualsFactStmt{params, line}
}

func NewKnowExistPropStmt(existProp *DefExistPropStmt, line uint) *KnowExistPropStmt {
	return &KnowExistPropStmt{existProp, line}
}

// func NewLatexStmt(comment string, line uint) *LatexStmt {
// 	return &LatexStmt{comment, line}
// }

func NewFnTemplateStmt(defHeader *DefHeader, templateDomFacts []FactStmt, fnTStruct *FnTStruct, line uint) *FnTemplateDefStmt {
	return &FnTemplateDefStmt{defHeader, templateDomFacts, fnTStruct, line}
}

func NewFnTStruct(params []string, paramSets []Obj, retSet Obj, domFacts []FactStmt, thenFacts []FactStmt, line uint) *FnTStruct {
	return &FnTStruct{params, paramSets, retSet, domFacts, thenFacts, line}
}

func NewClearStmt(line uint) *ClearStmt {
	return &ClearStmt{line}
}

func NewDoNothingStmt(line uint) *DoNothingStmt {
	return &DoNothingStmt{line}
}

func NewInlineFactsStmt(facts []FactStmt, line uint) *InlineFactsStmt {
	return &InlineFactsStmt{facts, line}
}

func NewProveByInductionStmt(fact *SpecFactStmt, param string, start Obj, line uint) *ProveByInductionStmt {
	return &ProveByInductionStmt{fact, param, start, line}
}

func NewHaveObjEqualStmt(objNames []string, objEqualTos []Obj, objSets []Obj, line uint) *HaveObjEqualStmt {
	return &HaveObjEqualStmt{objNames, objEqualTos, objSets, line}
}

func NewHaveFnEqualStmt(defHeader *DefHeader, retSet Obj, equalTo Obj, line uint) *HaveFnEqualStmt {
	return &HaveFnEqualStmt{defHeader, retSet, equalTo, line}
}

func NewHaveFnLiftStmt(fnName string, opt Obj, domainOfEachParamOfGivenFn []Obj, line uint) *HaveFnLiftStmt {
	return &HaveFnLiftStmt{fnName, opt, domainOfEachParamOfGivenFn, line}
}

func NewClaimHaveFnStmt(defFnStmt *DefFnStmt, proof []Stmt, haveObjSatisfyFn Obj, line uint) *HaveFnStmt {
	return &HaveFnStmt{defFnStmt, proof, haveObjSatisfyFn, line}
}

// func NewMarkdownStmt(comment string, line uint) *MarkdownStmt {
// 	return &MarkdownStmt{comment, line}
// }

// func NewProveInRange2Stmt(start int64, end int64, param string, domFacts ReversibleFacts, thenFacts []FactStmt, proofs []Stmt, line uint) *ProveInRange2tmt {
// 	return &ProveInRange2tmt{start, end, param, domFacts, thenFacts, proofs, line}
// }

func NewClaimIffStmt(uniFactWithIffStmt *UniFactWithIffStmt, proofs []Stmt, proofs2 []Stmt, line uint) *ClaimIffStmt {
	return &ClaimIffStmt{uniFactWithIffStmt, proofs, proofs2, line}
}

func NewProveInRangeSetStmt(start int64, end int64, param string, intensionalSet Obj, thenFacts []FactStmt, proofs []Stmt, line uint) *ProveInRangeSetStmt {
	return &ProveInRangeSetStmt{start, end, param, intensionalSet, thenFacts, proofs, line}
}

func NewProveInRangeStmt(param string, start Obj, end Obj, domFacts []FactStmt, thenFacts []FactStmt, proofs []Stmt, line uint) *ProveInRangeStmt {
	return &ProveInRangeStmt{param: param, start: start, end: end, DomFactsOrNil: domFacts, ThenFacts: thenFacts, ProofsOrNil: proofs, Line: line}
}

func NewProveIsTransitivePropStmt(prop Atom, params []string, proofs []Stmt, line uint) *ProveIsTransitivePropStmt {
	return &ProveIsTransitivePropStmt{prop, params, proofs, line}
}

func NewProveIsCommutativePropStmt(specFact *SpecFactStmt, proofs []Stmt, proofsRightToLeft []Stmt, line uint) *ProveIsCommutativePropStmt {
	return &ProveIsCommutativePropStmt{specFact, proofs, proofsRightToLeft, line}
}

func NewAlgoDefStmt(funcName string, params StrSlice, stmts AlgoStmtSlice, line uint) *DefAlgoStmt {
	return &DefAlgoStmt{funcName, params, stmts, line}
}

func NewAlgoIfStmt(condition []FactStmt, thenFacts AlgoStmtSlice, line uint) *AlgoIfStmt {
	return &AlgoIfStmt{condition, thenFacts, line}
}

func NewProveAlgoIfStmt(condition []FactStmt, thenFacts ProveAlgoStmtSlice, line uint) *ProveAlgoIfStmt {
	return &ProveAlgoIfStmt{condition, thenFacts, line}
}

func NewAlgoReturnStmt(value Obj, line uint) *AlgoReturnStmt {
	return &AlgoReturnStmt{value, line}
}

func NewUniFactWithSafeGuard(params []string, setParams []Obj, domFacts []FactStmt, thenFacts []FactStmt, line uint) (*UniFactStmt, error) {
	if len(thenFacts) == 0 {
		return nil, fmt.Errorf("expect %s section to have at least one fact in %s", glob.KeySymbolRightArrow, NewUniFact(params, setParams, domFacts, thenFacts, line))
	}

	for _, fact := range domFacts {
		params := ExtractParamsFromFact(fact)
		if params == nil {
			continue
		} else {
			for _, param := range params {
				if slices.Contains(params, param) {
					return nil, fmt.Errorf("parameter %s is duplicated in %s", param, fact.String())
				}
			}
		}
	}

	for _, fact := range thenFacts {
		params := ExtractParamsFromFact(fact)
		if params == nil {
			continue
		} else {
			for _, param := range params {
				if slices.Contains(params, param) {
					return nil, fmt.Errorf("parameter %s is duplicated in %s", param, fact.String())
				}
			}
		}
	}

	return NewUniFact(params, setParams, domFacts, thenFacts, line), nil
}

func NewUniFactWithIffWithSafeGuard(params []string, setParams []Obj, domFacts []FactStmt, thenFacts []FactStmt, iffFacts []FactStmt, line uint) (*UniFactWithIffStmt, error) {
	uniFact, err := NewUniFactWithSafeGuard(params, setParams, domFacts, thenFacts, line)
	if err != nil {
		return nil, err
	}

	if len(iffFacts) == 0 {
		return nil, fmt.Errorf("expect %s section to have at least one fact in %s", glob.KeySymbolRightArrow, NewUniFactWithIff(NewUniFact(params, setParams, domFacts, thenFacts, line), iffFacts, line))
	}

	for _, fact := range iffFacts {
		params := ExtractParamsFromFact(fact)
		if params == nil {
			continue
		} else {
			for _, param := range params {
				if slices.Contains(params, param) {
					return nil, fmt.Errorf("parameter %s is duplicated in %s", param, fact.String())
				}
			}
		}
	}

	return NewUniFactWithIff(uniFact, iffFacts, line), nil
}

func NewEvalStmt(value Obj, line uint) *EvalStmt {
	return &EvalStmt{value, line}
}

func NewDefProveAlgoStmt(algoName string, params []string, thenFacts ProveAlgoStmtSlice, line uint) *DefProveAlgoStmt {
	return &DefProveAlgoStmt{algoName, params, thenFacts, line}
}

func NewByStmt(proveAlgoName string, proveAlgoParams ObjSlice, line uint) *ByStmt {
	return &ByStmt{ProveAlgoName: proveAlgoName, Params: proveAlgoParams, Line: line}
}

func NewProveAlgoReturnStmt(facts FactOrByStmtSlice, line uint) *ProveAlgoReturnStmt {
	return &ProveAlgoReturnStmt{Facts: facts, Line: line}
}

func NewPrintStmt(isFString bool, value string, line uint) *PrintStmt {
	return &PrintStmt{isFString, value, line}
}

func NewHelpStmt(keyword string, line uint) *HelpStmt {
	return &HelpStmt{keyword, line}
}

func NewHaveFnCaseByCaseStmt(defFnStmt *DefFnStmt, caseByCaseFacts SpecFactPtrSlice, proofs StmtSliceSlice, haveObjSatisfyFn ObjSlice, line uint) *HaveFnCaseByCaseStmt {
	return &HaveFnCaseByCaseStmt{defFnStmt, caseByCaseFacts, proofs, haveObjSatisfyFn, line}
}

func NewHaveCartSetStmt(name string, cartObj *FnObj, line uint) *HaveCartSetStmt {
	return &HaveCartSetStmt{name, cartObj, line}
}

func NewHaveObjFromCartSetStmt(objName string, cartSet *FnObj, equalTo Obj, line uint) *HaveObjFromCartSetStmt {
	return &HaveObjFromCartSetStmt{objName, cartSet, equalTo, line}
}

func NewHaveCartWithDimStmt(objName string, cartDim Obj, param string, facts FactStmtSlice, proofs StmtSlice, equalTo Obj, line uint) *HaveCartWithDimStmt {
	return &HaveCartWithDimStmt{objName, cartDim, param, facts, proofs, equalTo, line}
}
