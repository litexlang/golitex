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

func newSpecFactMemDict() *SpecFactMem {
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

func (s SpecFactMem) NewFact(stmt *ast.SpecFactStmt) error {
	// 要考虑pkgName和propName是否存在
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
	}

	if _, ok := sameEnumFacts[stmt.PropName.PkgName]; !ok {
		sameEnumFacts[stmt.PropName.PkgName] = make(map[string][]KnownSpecFact)
	}
	if _, ok := sameEnumFacts[stmt.PropName.PkgName][stmt.PropName.Name]; !ok {
		sameEnumFacts[stmt.PropName.PkgName][stmt.PropName.Name] = []KnownSpecFact{}
	}
	sameEnumFacts[stmt.PropName.PkgName][stmt.PropName.Name] = append(sameEnumFacts[stmt.PropName.PkgName][stmt.PropName.Name], KnownSpecFact{stmt})

	return nil
}

type SpecFactInLogicExprMem struct {
	PureFacts         map[string]map[string][]KnownSpecFact_InLogicExpr
	NotPureFacts      map[string]map[string][]KnownSpecFact_InLogicExpr
	ExistFacts        map[string]map[string][]KnownSpecFact_InLogicExpr
	NotExistFacts     map[string]map[string][]KnownSpecFact_InLogicExpr
	Exist_St_Facts    map[string]map[string][]KnownSpecFact_InLogicExpr
	NotExist_St_Facts map[string]map[string][]KnownSpecFact_InLogicExpr
}

func NewSpecFactInLogicExprMemDict() *SpecFactInLogicExprMem {
	return &SpecFactInLogicExprMem{
		PureFacts:         map[string]map[string][]KnownSpecFact_InLogicExpr{},
		NotPureFacts:      map[string]map[string][]KnownSpecFact_InLogicExpr{},
		ExistFacts:        map[string]map[string][]KnownSpecFact_InLogicExpr{},
		NotExistFacts:     map[string]map[string][]KnownSpecFact_InLogicExpr{},
		Exist_St_Facts:    map[string]map[string][]KnownSpecFact_InLogicExpr{},
		NotExist_St_Facts: map[string]map[string][]KnownSpecFact_InLogicExpr{},
	}
}

func (s SpecFactInLogicExprMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]KnownSpecFact_InLogicExpr, bool) {
	var sameEnumFacts map[string]map[string][]KnownSpecFact_InLogicExpr
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

func (s SpecFactInLogicExprMem) NewFact(logicExpr *ast.LogicExprStmt) error {
	pairs, err := logicExpr.SpecFactIndexPairs([]uint8{})
	if err != nil {
		return err
	}

	for _, pair := range pairs {
		var sameEnumFacts map[string]map[string][]KnownSpecFact_InLogicExpr
		switch pair.Stmt.TypeEnum {
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
		}

		if _, ok := sameEnumFacts[pair.Stmt.PropName.PkgName]; !ok {
			sameEnumFacts[pair.Stmt.PropName.PkgName] = make(map[string][]KnownSpecFact_InLogicExpr)
		}
		if _, ok := sameEnumFacts[pair.Stmt.PropName.PkgName][pair.Stmt.PropName.Name]; !ok {
			sameEnumFacts[pair.Stmt.PropName.PkgName][pair.Stmt.PropName.Name] = []KnownSpecFact_InLogicExpr{}
		}

		sameEnumFacts[pair.Stmt.PropName.PkgName][pair.Stmt.PropName.Name] = append(sameEnumFacts[pair.Stmt.PropName.PkgName][pair.Stmt.PropName.Name], KnownSpecFact_InLogicExpr{pair.Stmt, pair.Indexes, logicExpr})
	}

	return nil
}
