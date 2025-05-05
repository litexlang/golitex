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

package litex_env

import ast "golitex/litex_ast"

type SpecFactMem struct {
	PureFacts         map[string]map[string][]KnownSpecFact
	NotPureFacts      map[string]map[string][]KnownSpecFact
	ExistFacts        map[string]map[string][]KnownSpecFact
	NotExistFacts     map[string]map[string][]KnownSpecFact
	Exist_St_Facts    map[string]map[string][]KnownSpecFact
	NotExist_St_Facts map[string]map[string][]KnownSpecFact
}

func NewSpecFactMemDict() *SpecFactMem {
	return &SpecFactMem{
		PureFacts:         map[string]map[string][]KnownSpecFact{},
		NotPureFacts:      map[string]map[string][]KnownSpecFact{},
		ExistFacts:        map[string]map[string][]KnownSpecFact{},
		NotExistFacts:     map[string]map[string][]KnownSpecFact{},
		Exist_St_Facts:    map[string]map[string][]KnownSpecFact{},
		NotExist_St_Facts: map[string]map[string][]KnownSpecFact{},
	}
}

func (s SpecFactMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]KnownSpecFact, bool) {
	var sameEnumFacts map[string]map[string][]KnownSpecFact
	switch stmt.TypeEnum {
	case ast.TrueAtom:
		sameEnumFacts = s.PureFacts
	case ast.FalseAtom:
		sameEnumFacts = s.NotPureFacts
	case ast.TrueExist:
		sameEnumFacts = s.ExistFacts
	case ast.FalseExist:
		sameEnumFacts = s.NotExistFacts
	case ast.TrueExist_St:
		sameEnumFacts = s.Exist_St_Facts
	case ast.FalseExist_St:
		sameEnumFacts = s.NotExist_St_Facts
	default:
		return nil, false
	}

	sameEnumPkgfacts, memExist := sameEnumFacts[stmt.PropName.PkgName]
	if !memExist {
		return nil, false
	}

	sameEnumPkgPropFacts, memExist := sameEnumPkgfacts[stmt.PropName.Name]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFactMem) NewFact(stmt *ast.SpecFactStmt) {
	// 要考虑pkgName和propName是否存在
	if _, ok := s.PureFacts[stmt.PropName.PkgName]; !ok {
		s.PureFacts[stmt.PropName.PkgName] = make(map[string][]KnownSpecFact)
	}
	if _, ok := s.PureFacts[stmt.PropName.PkgName][stmt.PropName.Name]; !ok {
		s.PureFacts[stmt.PropName.PkgName][stmt.PropName.Name] = []KnownSpecFact{}
	}
	s.PureFacts[stmt.PropName.PkgName][stmt.PropName.Name] = append(s.PureFacts[stmt.PropName.PkgName][stmt.PropName.Name], KnownSpecFact{stmt})
}

type SpecFactInLogicExprMem struct {
	PureFacts         map[string]map[string][]KnownSpecFact_InLogicExpr
	NotPureFacts      map[string]map[string][]KnownSpecFact_InLogicExpr
	ExistFacts        map[string]map[string][]KnownSpecFact_InLogicExpr
	NotExistFacts     map[string]map[string][]KnownSpecFact_InLogicExpr
	Exist_St_Facts    map[string]map[string][]KnownSpecFact_InLogicExpr
	NotExist_St_Facts map[string]map[string][]KnownSpecFact_InLogicExpr
}
