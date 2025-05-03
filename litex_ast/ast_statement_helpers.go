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

func (stmt *SpecFactStmt) IsBuiltinInfixRelaProp() bool {
	return stmt.PropName.PkgName == glob.BuiltinEmptyPkgName && glob.IsBuiltinInfixRelaProp(stmt.PropName.Name)
}

func (stmt *UniFactStmt) NewUniFactWithThenToIff() *UniFactStmt {
	newConUniFact := newConUniFactStmt(stmt.Params, stmt.ParamSets, stmt.DomFacts, stmt.IffFacts, EmptyIffFacts)
	newConUniFact.DomFacts = append(newConUniFact.DomFacts, stmt.ThenFacts...)
	return newConUniFact
}

func (stmt *UniFactStmt) NewUniFactWithIffToThen() *UniFactStmt {
	newConUniFact := newConUniFactStmt(stmt.Params, stmt.ParamSets, stmt.DomFacts, stmt.ThenFacts, EmptyIffFacts)
	newConUniFact.DomFacts = append(newConUniFact.DomFacts, stmt.IffFacts...)
	return newConUniFact
}

func MergeOuterInnerUniFacts(outer *UniFactStmt, inner *UniFactStmt) *UniFactStmt {
	newOuter := newConUniFactStmt(outer.Params, outer.ParamSets, outer.DomFacts, inner.ThenFacts, EmptyIffFacts)
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

func AddUniPrefixToUniFactWithNoUniPrefix(asConUniFact *UniFactStmt) (*UniFactStmt, error) {
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

	newUniFact := newConUniFactStmt(newParams, newParamsSets, newDomFacts, newThenFacts, newIffFacts)

	return newUniFact, nil
}

func IsUniParam(fcAtom *FcAtom) (string, bool) {
	if strings.HasPrefix(fcAtom.Name, glob.UniParamPrefix) && fcAtom.PkgName == glob.BuiltinEmptyPkgName {
		return fcAtom.Name, true
	}
	return "", false
}

func (stmt *SpecFactStmt) IsPropNameCommutative() bool {
	return stmt.PropName.PkgName == glob.BuiltinEmptyPkgName && glob.KeywordCommutative == stmt.PropName.Name
}

func (stmt *SpecFactStmt) IsPropNameAssociative() bool {
	return stmt.PropName.PkgName == glob.BuiltinEmptyPkgName && glob.KeywordAssociative == stmt.PropName.Name
}

var notFcAtomNameSet = map[string]struct{}{
	// 常规关键字
	glob.KeywordForall: {},
	// glob.KeywordWhen:     {},
	glob.KeywordDom:      {},
	glob.KeywordThen:     {},
	glob.KeywordExistObj: {},
	glob.KeywordSt:       {},
	// glob.KeywordConstructorProp:      {},
	glob.KeywordClaim:                {},
	glob.KeywordProve:                {},
	glob.KeywordPub:                  {},
	glob.KeywordImport:               {},
	glob.KeywordPackage:              {},
	glob.KeywordNot:                  {},
	glob.KeywordAxiom:                {},
	glob.KeywordProveByContradiction: {},
	glob.KeywordThm:                  {},
	glob.KeywordIff:                  {},
	glob.KeywordExist:                {},
}

func IsNotFcAtomName(s string) bool {
	_, ok := notFcAtomNameSet[s]
	return ok || glob.IsKeySymbol(s)
}

var BuiltinKwFcNames = map[string]struct{}{
	glob.KeywordNatural:   {},
	glob.KeywordSet:       {},
	glob.KeywordObj:       {},
	glob.KeywordReal:      {},
	glob.KeywordFn:        {},
	glob.KeywordProp:      {},
	glob.KeywordExistProp: {},
	glob.KeywordInt:       {},
	glob.KeywordRational:  {},
}

func IsBuiltinKwFcAtom(fc *FcAtom) bool {
	if fc.PkgName == glob.BuiltinEmptyPkgName {
		_, ok := BuiltinKwFcNames[fc.Name]
		return ok
	}
	return false
}

var InFc = NewFcAtom(glob.BuiltinEmptyPkgName, glob.KeywordIn)

func NewConUniFactStmtWithSetReqPutIntoDom(params []string, paramTypes []Fc, domFacts []FactStmt, thenFacts []FactStmt, iffFacts []FactStmt) *UniFactStmt {
	if glob.VerifyFcSatisfySpecFactParaReq {
		newDomFacts := []FactStmt{}
		for i, param := range params {
			atom := NewFcAtom(glob.BuiltinEmptyPkgName, param)
			specFact := NewSpecFactStmt(TrueAtom, *InFc, []Fc{atom, paramTypes[i]})
			newDomFacts = append(newDomFacts, specFact)
		}
		newDomFacts = append(newDomFacts, domFacts...)
		newConUniFact := newConUniFactStmt(params, paramTypes, newDomFacts, thenFacts, iffFacts)
		return newConUniFact
	}
	return newConUniFactStmt(params, paramTypes, domFacts, thenFacts, iffFacts)
}

func IsBuiltinFnName(fc Fc) bool {
	fcAtom, ok := fc.(*FcAtom)
	if !ok {
		return false
	}

	if fcAtom.PkgName != glob.BuiltinEmptyPkgName {
		return false
	}

	return glob.IsBuiltinInfixRelaProp(fcAtom.Name)
}

func IsInProp(fc *FcAtom) bool {
	return fc.Name == glob.KeywordIn && fc.PkgName == glob.BuiltinEmptyPkgName
}

func IsNatFcAtom(fc Fc) bool {
	fcAtom, ok := fc.(*FcAtom)
	if !ok {
		return false
	}
	return fcAtom.Name == glob.KeywordNatural && fcAtom.PkgName == glob.BuiltinEmptyPkgName
}

func IsIntegerFcAtom(fc Fc) bool {
	fcAtom, ok := fc.(*FcAtom)
	if !ok {
		return false
	}
	return fcAtom.Name == glob.KeywordInt && fcAtom.PkgName == glob.BuiltinEmptyPkgName
}

func IsRationalFcAtom(fc Fc) bool {
	fcAtom, ok := fc.(*FcAtom)
	if !ok {
		return false
	}
	return fcAtom.Name == glob.KeywordRational && fcAtom.PkgName == glob.BuiltinEmptyPkgName
}

func IsRealFcAtom(fc Fc) bool {
	fcAtom, ok := fc.(*FcAtom)
	if !ok {
		return false
	}
	return fcAtom.Name == glob.KeywordReal && fcAtom.PkgName == glob.BuiltinEmptyPkgName
}

func (defStmt *DefConPropStmt) PropDefToUniFacts() (*UniFactStmt, *UniFactStmt, error) {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.BuiltinEmptyPkgName, param))
	}

	propSpecFact := NewSpecFactStmt(TrueAtom, FcAtom{glob.BuiltinEmptyPkgName, defStmt.DefHeader.Name}, propSpecFactParams)

	// prop to iff
	propToIffDomFacts := []FactStmt{propSpecFact}
	propToIffDomFacts = append(propToIffDomFacts, defStmt.DomFacts...)

	propToIff := NewConUniFactStmtWithSetReqPutIntoDom(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, propToIffDomFacts, defStmt.IffFacts, EmptyIffFacts)

	// iff to prop
	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFacts...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFacts...)

	IffToProp := NewConUniFactStmtWithSetReqPutIntoDom(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, IffToPropDomFacts, []FactStmt{propSpecFact}, EmptyIffFacts)

	return propToIff, IffToProp, nil
}

func (defStmt *DefConPropStmt) IffToPropUniFact() *UniFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.BuiltinEmptyPkgName, param))
	}

	propSpecFact := NewSpecFactStmt(TrueAtom, FcAtom{glob.BuiltinEmptyPkgName, defStmt.DefHeader.Name}, propSpecFactParams)

	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFacts...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFacts...)

	IffToProp := NewConUniFactStmtWithSetReqPutIntoDom(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, IffToPropDomFacts, []FactStmt{propSpecFact}, EmptyIffFacts)

	return IffToProp
}

func (fact *SpecFactStmt) IsSpecFactNameWithUniPrefix() bool {
	return strings.HasPrefix(fact.PropName.Name, glob.UniParamPrefix)
}

var EmptyIffFacts []FactStmt = nil

var ClaimStmtEmptyToCheck FactStmt = nil
