// Copyright Jiachen Shen.
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

// func NewDefExistPropStmt(def *DefExistPropStmtBody, existParams []string, existParamSets []Obj, line uint) *DefExistPropStmt {
// 	return &DefExistPropStmt{def, existParams, existParamSets, line}
// }

func NewSpecFactStmt(typeEnum SpecFactType, propName Atom, params []Obj, line uint) *SpecFactStmt {
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

func NewDefHeader(name string, params []string, setParams []Obj) *DefHeader {
	return &DefHeader{name, params, setParams}
}

// func NewHaveObjStStmt(objNames []string, fact *SpecFactStmt, line uint) *HaveObjStStmt {
// 	return &HaveObjStStmt{objNames, fact, line}
// }

func NewHaveObjStWithParamSetsStmt(objNames []string, objSets []Obj, fact *SpecFactStmt, line uint) *HaveObjStWithParamSetsStmt {
	return &HaveObjStWithParamSetsStmt{objNames, objSets, fact, line}
}

// func NewExistPropDef(declHeader *DefHeader, domFacts []FactStmt, iffFacts []FactStmt, thenFacts []FactStmt, line uint) *DefExistPropStmtBody {
// 	return &DefExistPropStmtBody{declHeader, domFacts, iffFacts, thenFacts, line}
// }

func NewUniFact(params []string, setParams []Obj, domFacts []FactStmt, thenFacts []FactStmt, line uint) *UniFactStmt {
	return &UniFactStmt{params, setParams, domFacts, thenFacts, line}
}

func NewUniFactWithIff(uniFact *UniFactStmt, iffFacts []FactStmt, line uint) *UniFactWithIffStmt {
	return &UniFactWithIffStmt{uniFact, iffFacts, line}
}

func NewProveCaseByCaseStmt(caseFacts []*SpecFactStmt, thenFacts []FactStmt, proofs StmtSliceSlice, line uint) *ProveCaseByCaseStmt {
	return &ProveCaseByCaseStmt{caseFacts, thenFacts, proofs, line}
}

func NewKnowImplicationStmt(prop *DefPropStmt, line uint) *KnowImplicationStmt {
	return &KnowImplicationStmt{prop, line}
}

// func NewDefExistPropBodyStmt(defHeader *DefHeader, domFacts []FactStmt, iffFacts []FactStmt, thenFacts []FactStmt, line uint) *DefExistPropStmtBody {
// 	return &DefExistPropStmtBody{defHeader, domFacts, iffFacts, thenFacts, line}
// }

func NewOrStmt(orFacts []*SpecFactStmt, line uint) *OrStmt {
	return &OrStmt{orFacts, line}
}

func NewImportDirStmt(path string, asPkgName string, IsGlobalPkg bool, line uint) *ImportDirStmt {
	return &ImportDirStmt{path, asPkgName, IsGlobalPkg, line}
}

func NewProveStmt(proof []Stmt, line uint) *ProveStmt {
	return &ProveStmt{proof, line}
}

func NewLetFnStmt(name string, fnTemplate *AnonymousFn, line uint) *LetFnStmt {
	return &LetFnStmt{name, fnTemplate, line}
}

// func NewEnumStmt(enumName Obj, enumValues []Obj, line uint) *EnumStmt {
// 	return &EnumStmt{enumName, enumValues, line}
// }

func NewRunFileStmt(path string, line uint) *RunFileStmt {
	return &RunFileStmt{path, line}
}

func NewClaimPropStmt(implication *DefPropStmt, proofs []Stmt, line uint) *ClaimImplicationStmt {
	return &ClaimImplicationStmt{implication, proofs, line}
}

// func NewClaimExistPropStmt(existProp *DefExistPropStmt, proofs []Stmt, haveObj []Obj, line uint) *ClaimExistPropStmt {
// 	return &ClaimExistPropStmt{existProp, proofs, haveObj, line}
// }

func NewProveByEnumStmt(fact *UniFactStmt, proofs []Stmt, line uint) *ProveByEnumStmt {
	return &ProveByEnumStmt{fact, proofs, line}
}

func NewHaveObjInNonEmptySetStmt(objNames []string, objSets []Obj, line uint) *HaveObjInNonEmptySetStmt {
	return &HaveObjInNonEmptySetStmt{objNames, objSets, line}
}

// func NewNamedUniFactStmt(defPropStmt *DefPropStmt, line uint) *NamedUniFactStmt {
// 	return &NamedUniFactStmt{defPropStmt, line}
// }

func NewEqualsFactStmt(params ObjSlice, line uint) *EqualsFactStmt {
	return &EqualsFactStmt{params, line}
}

// func NewKnowExistPropStmt(existProp *DefExistPropStmt, line uint) *KnowExistPropStmt {
// 	return &KnowExistPropStmt{existProp, line}
// }

func NewDefFnSetStmt(defHeader *DefHeader, templateDomFacts []FactStmt, fnTStruct *AnonymousFn, line uint) *DefFnSetStmt {
	return &DefFnSetStmt{defHeader, templateDomFacts, fnTStruct, line}
}

func NewFnTStruct(params []string, paramSets []Obj, retSet Obj, domFacts []FactStmt, thenFacts []FactStmt, line uint) *AnonymousFn {
	return &AnonymousFn{params, paramSets, retSet, domFacts, thenFacts, line}
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

// func NewHaveFnLiftStmt(fnName string, opt Obj, domainOfEachParamOfGivenFn []Obj, line uint) *HaveFnLiftStmt {
// 	return &HaveFnLiftStmt{fnName, opt, domainOfEachParamOfGivenFn, line}
// }

func NewClaimHaveFnStmt(defFnStmt *LetFnStmt, proof []Stmt, haveObjSatisfyFn Obj, line uint) *HaveFnStmt {
	return &HaveFnStmt{defFnStmt, proof, haveObjSatisfyFn, line}
}

// func NewMarkdownStmt(comment string, line uint) *MarkdownStmt {
// 	return &MarkdownStmt{comment, line}
// }

func NewClaimIffStmt(uniFactWithIffStmt *UniFactWithIffStmt, proofs []Stmt, proofs2 []Stmt, line uint) *ClaimIffStmt {
	return &ClaimIffStmt{uniFactWithIffStmt, proofs, proofs2, line}
}

func NewProveForStmt(params []string, lefts []Obj, rights []Obj, isProveIRange []bool, domFacts []FactStmt, thenFacts []FactStmt, proofs []Stmt, line uint) *ProveForStmt {
	return &ProveForStmt{Params: params, Lefts: lefts, Rights: rights, IsProveIRange: isProveIRange, DomFacts: domFacts, ThenFacts: thenFacts, Proofs: proofs, Line: line}
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

func NewHaveFnCaseByCaseStmt(defFnStmt *LetFnStmt, caseByCaseFacts SpecFactPtrSlice, proofs StmtSliceSlice, haveObjSatisfyFn ObjSlice, line uint) *HaveFnCaseByCaseStmt {
	return &HaveFnCaseByCaseStmt{defFnStmt, caseByCaseFacts, proofs, haveObjSatisfyFn, line}
}

// func NewHaveObjFromCartSetStmt(objName string, cartSet *FnObj, equalTo Obj, line uint) *HaveObjFromCartSetStmt {
// 	return &HaveObjFromCartSetStmt{objName, cartSet, equalTo, line}
// }

func NewProveImplicationStmt(specFact *SpecFactStmt, implicationFact FactStmtSlice, proof StmtSlice, line uint) *ProveImplyStmt {
	return &ProveImplyStmt{specFact, implicationFact, proof, line}
}

// func NewImplicationStmt(defHeader *DefHeader, domFacts FactStmtSlice, implicationFacts FactStmtSlice, line uint) *DefImplicationStmt {
// 	return &DefImplicationStmt{defHeader, domFacts, implicationFacts, line}
// }

func NewProveExistStmt(params []string, paramSets []Obj, equalTos []Obj, fact *SpecFactStmt, proofs []Stmt, line uint) *ProveExistStmt {
	return &ProveExistStmt{params, paramSets, equalTos, fact, proofs, line}
}
