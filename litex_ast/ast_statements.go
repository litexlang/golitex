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

type TopStmt struct {
	Stmt  Stmt
	IsPub bool
}

type DefObjStmt struct {
	Objs    []string
	ObjSets []Fc
	Facts   []FactStmt
}

type ConDefHeader struct {
	Name      string
	Params    []string
	SetParams []Fc
}

type DefConPropStmt struct {
	DefHeader ConDefHeader
	DomFacts  []FactStmt // 如果输入的参数不满足dom，那就是error
	// IffFacts []*SpecFactStmt
	IffFacts []FactStmt
}

type ExistPropDef struct {
	DefHeader ConDefHeader
	DomFacts  []FactStmt
	IffFacts  []*SpecFactStmt // 必须是 iff，因为 not exist XXX <=> forall not XXX，而 not XXX 要求 XXX 是 spec
}

type DefConExistPropStmt struct {
	Def            ExistPropDef
	ExistParams    []string
	ExistParamSets []Fc
}

type DefConFnStmt struct {
	DefHeader ConDefHeader
	RetSet    Fc
	DomFacts  []FactStmt
	// ThenFacts []*SpecFactStmt
	ThenFacts []FactStmt
}

type UniFactStmt struct {
	Params    []string // 它可能也是来自另外一个被share的地方。比如defConFn里面的Params，在被存成facts的时候，整个struct被复制到了这里，但本质上它们共享了一片内存
	ParamSets []Fc
	DomFacts  []FactStmt
	ThenFacts []FactStmt
	IffFacts  []FactStmt // TODO: 需要注意到，我存储的所有事实，这一项都是空。未来为了节约空间，可以考虑用新的结构体来存储
}

type SpecFactStmt struct {
	TypeEnum SpecFactEnum
	PropName FcAtom
	Params   []Fc
}

type ClaimStmt struct {
	IsProve     bool
	ToCheckFact FactStmt
	Proofs      []Stmt
	ClaimName   string // 有时候有，有时候没有
}

type KnowStmt struct {
	Facts []FactStmt
}

// syntax sugar for defining spec prop + claim forall true
type AxiomStmt struct {
	Name string
	Fact UniFactStmt
}

type FcFnDecl struct {
	Name   string
	Params []string
}

type LogicExprStmt struct {
	IsOr  bool
	Facts []LogicExprOrSpecFactStmt
}

type ExistObjDefStmt struct {
	ObjNames []string
	Fact     SpecFactStmt
}

type SetDefSetBuilderStmt struct {
	SetName   string
	ParentSet Fc
	Facts     []FactStmt
}

type SetDefEnumtmt struct {
	SetName string
	Elems   []Fc
}

type MatcherEnvStmt struct {
	MatcherName FcAtom // pkgName::matcherName
	Params      []Fc
	Body        []Stmt
}

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

func (stmt *SpecFactStmt) IsPropNameCommutative() bool {
	return stmt.PropName.PkgName == glob.BuiltinEmptyPkgName && glob.KeywordCommutative == stmt.PropName.Name
}

func (stmt *SpecFactStmt) IsPropNameAssociative() bool {
	return stmt.PropName.PkgName == glob.BuiltinEmptyPkgName && glob.KeywordAssociative == stmt.PropName.Name
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

	propToIff := NewUniFactStmtWithSetReqInDom(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, propToIffDomFacts, defStmt.IffFacts, EmptyIffFacts)

	// iff to prop
	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFacts...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFacts...)

	IffToProp := NewUniFactStmtWithSetReqInDom(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, IffToPropDomFacts, []FactStmt{propSpecFact}, EmptyIffFacts)

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

	IffToProp := NewUniFactStmtWithSetReqInDom(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, IffToPropDomFacts, []FactStmt{propSpecFact}, EmptyIffFacts)

	return IffToProp
}

func (fact *SpecFactStmt) IsSpecFactNameWithUniPrefix() bool {
	return strings.HasPrefix(fact.PropName.Name, glob.UniParamPrefix)
}

func (defStmt *DefConPropStmt) ToSpecFact() *SpecFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.BuiltinEmptyPkgName, param))
	}

	propSpecFact := NewSpecFactStmt(TrueAtom, FcAtom{glob.BuiltinEmptyPkgName, defStmt.DefHeader.Name}, propSpecFactParams)

	return propSpecFact
}

func (stmt *SpecFactStmt) ReverseParameterOrder() (*SpecFactStmt, error) {
	if len(stmt.Params) != 2 {
		return nil, fmt.Errorf("reverseParameterOrder: expected 2 params, but got %d", len(stmt.Params))
	}

	newParams := []Fc{stmt.Params[1], stmt.Params[0]}

	return NewSpecFactStmt(stmt.TypeEnum, stmt.PropName, newParams), nil
}
