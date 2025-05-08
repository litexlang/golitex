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
	glob "golitex/glob"
	"strings"
)

func (stmt *SpecFactStmt) IsBuiltinInfixRelaProp() bool {
	return stmt.PropName.PkgName == glob.BtEmptyPkgName && glob.IsBuiltinInfixRelaProp(stmt.PropName.Name)
}

func (stmt *UniFactStmt) NewUniFactWithThenToIff() *UniFactStmt {
	newUniFact := newUniFactStmt(stmt.Params, stmt.ParamSets, stmt.DomFacts, stmt.IffFacts, EmptyIffFacts)
	newUniFact.DomFacts = append(newUniFact.DomFacts, stmt.ThenFacts...)
	return newUniFact
}

func (stmt *UniFactStmt) NewUniFactWithIffToThen() *UniFactStmt {
	newUniFact := newUniFactStmt(stmt.Params, stmt.ParamSets, stmt.DomFacts, stmt.ThenFacts, EmptyIffFacts)
	newUniFact.DomFacts = append(newUniFact.DomFacts, stmt.IffFacts...)
	return newUniFact
}

func MergeOuterInnerUniFacts(outer *UniFactStmt, inner *UniFactStmt) *UniFactStmt {
	newOuter := newUniFactStmt(outer.Params, outer.ParamSets, outer.DomFacts, inner.ThenFacts, EmptyIffFacts)
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

func (defStmt *DefPropStmt) MakeUniFacts() (*UniFactStmt, *UniFactStmt, error) {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.BtEmptyPkgName, param))
	}

	propSpecFact := NewSpecFactStmt(TrueAtom, FcAtom{glob.BtEmptyPkgName, defStmt.DefHeader.Name}, propSpecFactParams)

	// prop to iff
	propToIffDomFacts := []FactStmt{propSpecFact}
	propToIffDomFacts = append(propToIffDomFacts, defStmt.DomFacts...)

	propToIff := NewUniFactStmtWithSetReqInDom(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, propToIffDomFacts, defStmt.IffFacts, EmptyIffFacts)

	// iff to prop
	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFacts...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFacts...)

	IffToProp := NewUniFactStmtWithSetReqInDom(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, IffToPropDomFacts, []FactStmt{propSpecFact}, EmptyIffFacts)

	return propToIff, IffToProp, nil
}

func (defStmt *DefPropStmt) IffToPropUniFact() *UniFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.BtEmptyPkgName, param))
	}

	propSpecFact := NewSpecFactStmt(TrueAtom, FcAtom{glob.BtEmptyPkgName, defStmt.DefHeader.Name}, propSpecFactParams)

	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFacts...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFacts...)

	IffToProp := NewUniFactStmtWithSetReqInDom(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, IffToPropDomFacts, []FactStmt{propSpecFact}, EmptyIffFacts)

	return IffToProp
}

func (fact *SpecFactStmt) IsSpecFactNameWithUniPrefix() bool {
	return strings.HasPrefix(fact.PropName.Name, glob.UniParamPrefix)
}

func (defStmt *DefPropStmt) ToSpecFact() *SpecFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.BtEmptyPkgName, param))
	}

	propSpecFact := NewSpecFactStmt(TrueAtom, FcAtom{glob.BtEmptyPkgName, defStmt.DefHeader.Name}, propSpecFactParams)

	return propSpecFact
}

func (stmt *SpecFactStmt) ReverseParameterOrder() (*SpecFactStmt, error) {
	if len(stmt.Params) != 2 {
		return nil, fmt.Errorf("reverseParameterOrder: expected 2 params, but got %d", len(stmt.Params))
	}

	newParams := []Fc{stmt.Params[1], stmt.Params[0]}

	return NewSpecFactStmt(stmt.TypeEnum, stmt.PropName, newParams), nil
}
