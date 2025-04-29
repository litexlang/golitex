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
	"fmt"
	glob "golitex/litex_global"
	"strings"
)

type SpecFactEnum uint8

const (
	TrueAtom SpecFactEnum = iota
	FalseAtom
	TrueExist
	FalseExist
	TrueExist_St
	FalseExist_St
)

func (stmt *SpecFactStmt) ReverseIsTrue() *SpecFactStmt {
	if stmt.TypeEnum == TrueAtom {
		return NewSpecFactStmt(FalseAtom, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == FalseAtom {
		return NewSpecFactStmt(TrueAtom, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == TrueExist {
		return NewSpecFactStmt(FalseExist, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == FalseExist {
		return NewSpecFactStmt(TrueExist, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == TrueExist_St {
		return NewSpecFactStmt(FalseExist_St, stmt.PropName, stmt.Params)
	} else if stmt.TypeEnum == FalseExist_St {
		return NewSpecFactStmt(TrueExist_St, stmt.PropName, stmt.Params)
	}
	panic("unknown spec fact type")
}

func (f *SpecFactStmt) IsEqualFact() bool {
	return f.PropName.Name == glob.KeySymbolEqual && f.PropName.PkgName == glob.BuiltinEmptyPkgName
}

func (f *SpecFactStmt) IsExistFact() bool {
	return f.TypeEnum == TrueExist || f.TypeEnum == FalseExist
}

func (f *SpecFactStmt) IsExist_St_Fact() bool {
	return f.TypeEnum == TrueExist_St || f.TypeEnum == FalseExist_St
}

func (f *SpecFactStmt) IsTrue() bool {
	return f.TypeEnum == TrueAtom || f.TypeEnum == TrueExist || f.TypeEnum == TrueExist_St
}

func (f *SpecFactStmt) Exist_St_SeparatorIndex() int {
	for i, param := range f.Params {
		paramAsAtom, ok := param.(*FcAtom)
		if ok && paramAsAtom.PkgName == glob.BuiltinEmptyPkgName && paramAsAtom.Name == glob.BuiltinExist_St_FactExistParamPropParmSep {
			return i
		}
	}
	return -1
}

type SpecFactIndexInLogicExprPair struct {
	Stmt    *SpecFactStmt
	Indexes []uint8
}

func (stmt *LogicExprStmt) SpecFactIndexPairs(indexes []uint8) ([]SpecFactIndexInLogicExprPair, error) {
	pairs := []SpecFactIndexInLogicExprPair{}
	for i, fact := range stmt.Facts {
		if specFact, ok := fact.(*SpecFactStmt); ok {
			curIndexes := make([]uint8, len(indexes))
			copy(curIndexes, indexes)
			curIndexes = append(curIndexes, uint8(i))
			pairs = append(pairs, SpecFactIndexInLogicExprPair{specFact, curIndexes})
			continue
		}

		if logicExpr, ok := fact.(*LogicExprStmt); ok {
			curIndexes := make([]uint8, len(indexes))
			copy(curIndexes, indexes)
			currentPairs, err := logicExpr.SpecFactIndexPairs(curIndexes)
			if err != nil {
				return nil, err
			}
			pairs = append(pairs, currentPairs...)
			continue
		}
	}
	if len(pairs) > glob.MaxLogicExprStmtIndexesSize {
		return nil, fmt.Errorf("logic expr stmt size too large")
	}
	return pairs, nil
}

var SpecFactUnderNoLogicalExprSig []uint8 = nil

func (stmt *SpecFactStmt) IsBuiltinLogicOpt() bool {
	return stmt.PropName.PkgName == glob.BuiltinEmptyPkgName && glob.IsBuiltinInfixRelaProp(stmt.PropName.Name)
}

func (stmt *ConUniFactStmt) NewUniFactWithThenToIff() *ConUniFactStmt {
	newConUniFact := NewConUniFactStmt(stmt.Params, stmt.ParamSets, stmt.DomFacts, stmt.IffFacts, EmptyIffFacts)
	newConUniFact.DomFacts = append(newConUniFact.DomFacts, stmt.ThenFacts...)
	return newConUniFact
}

func (stmt *ConUniFactStmt) NewUniFactWithIffToThen() *ConUniFactStmt {
	newConUniFact := NewConUniFactStmt(stmt.Params, stmt.ParamSets, stmt.DomFacts, stmt.ThenFacts, EmptyIffFacts)
	newConUniFact.DomFacts = append(newConUniFact.DomFacts, stmt.IffFacts...)
	return newConUniFact
}

func MergeOuterInnerUniFacts(outer *ConUniFactStmt, inner *ConUniFactStmt) *ConUniFactStmt {
	newOuter := NewConUniFactStmt(outer.Params, outer.ParamSets, outer.DomFacts, inner.ThenFacts, EmptyIffFacts)
	newOuter.Params = append(newOuter.Params, inner.Params...)
	newOuter.ParamSets = append(newOuter.ParamSets, inner.ParamSets...)
	newOuter.DomFacts = append(newOuter.DomFacts, inner.DomFacts...)
	return newOuter
}

func GetStrParamsWithUniPrefixAndNewDepthMap(originalParams []string, originalNameDepthMap NameDepthMap) ([]string, NameDepthMap) {
	newUniParams := NameDepthMap{}
	for key := range originalNameDepthMap {
		newUniParams[key] = originalNameDepthMap[key]
	}

	newParams := make([]string, len(originalParams))

	for i := range originalParams {
		prefixNum, declared := originalNameDepthMap[originalParams[i]]
		if !declared {
			newUniParams[originalParams[i]] = 1
			newParams[i] = fmt.Sprintf("%s%s", glob.UniParamPrefix, originalParams[i])
		} else {
			newUniParams[originalParams[i]] = prefixNum + 1
			newParams[i] = fmt.Sprintf("%s%s", strings.Repeat(glob.UniParamPrefix, prefixNum+1), originalParams[i])
		}
	}

	return newParams, newUniParams
}

func AddUniPrefixToUniFactWithNoUniPrefix(asConUniFact *ConUniFactStmt) (*ConUniFactStmt, error) {
	uniConMap := map[string]Fc{}
	newParams := make([]string, len(asConUniFact.Params))

	for i, param := range asConUniFact.Params {
		newParams[i] = fmt.Sprintf("%s%s", glob.UniParamPrefix, param)
		uniConMap[param] = NewFcAtom(glob.BuiltinEmptyPkgName, newParams[i])
	}

	newParamsSets := asConUniFact.ParamSets
	newDomFacts := []FactStmt{}
	newThenFacts := []FactStmt{}
	newIffFacts := EmptyIffFacts

	for _, fact := range asConUniFact.DomFacts {
		newFact, err := fact.Instantiate(uniConMap)
		if err != nil {
			return nil, err
		}
		newDomFacts = append(newDomFacts, newFact)
	}

	for _, fact := range asConUniFact.ThenFacts {
		newFact, err := fact.Instantiate(uniConMap)
		if err != nil {
			return nil, err
		}
		newThenFacts = append(newThenFacts, newFact)
	}

	newUniFact := NewConUniFactStmt(newParams, newParamsSets, newDomFacts, newThenFacts, newIffFacts)

	return newUniFact, nil
}
