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

import (
	"errors"
	"fmt"
	ast "golitex/litex_ast"
)

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

func (s SpecFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string]map[string][]KnownSpecFact, error) {
	switch stmt.TypeEnum {
	case ast.TrueAtom:
		return s.PureFacts, nil
	case ast.FalseAtom:
		return s.NotPureFacts, nil
	case ast.TrueExist:
		return s.ExistFacts, nil
	case ast.FalseExist:
		return s.NotExistFacts, nil
	case ast.TrueExist_St:
		return s.Exist_St_Facts, nil
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, nil
	default:
		return nil, errors.New("invalid spec fact type")
	}
}

func (s SpecFactMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]KnownSpecFact, bool) {
	sameEnumFacts, err := s.getSameEnumFacts(stmt)
	if err != nil {
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
	sameEnumFacts, err := s.getSameEnumFacts(stmt)
	if err != nil {
		return err
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

func (s SpecFactInLogicExprMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string]map[string][]KnownSpecFact_InLogicExpr, error) {
	switch stmt.TypeEnum {
	case ast.TrueAtom:
		return s.PureFacts, nil
	case ast.FalseAtom:
		return s.NotPureFacts, nil
	case ast.TrueExist:
		return s.ExistFacts, nil
	case ast.FalseExist:
		return s.NotExistFacts, nil
	case ast.TrueExist_St:
		return s.Exist_St_Facts, nil
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, nil
	default:
		return nil, errors.New("invalid spec fact type")
	}
}

func (s SpecFactInLogicExprMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]KnownSpecFact_InLogicExpr, bool) {
	sameEnumFacts, err := s.getSameEnumFacts(stmt)
	if err != nil {
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
		sameEnumFacts, err := s.getSameEnumFacts(pair.Stmt)
		if err != nil {
			return err
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

type SpecFactInUniFactMem struct {
	PureFacts         map[string]map[string][]KnownSpecFact_InUniSpecFact
	NotPureFacts      map[string]map[string][]KnownSpecFact_InUniSpecFact
	ExistFacts        map[string]map[string][]KnownSpecFact_InUniSpecFact
	NotExistFacts     map[string]map[string][]KnownSpecFact_InUniSpecFact
	Exist_St_Facts    map[string]map[string][]KnownSpecFact_InUniSpecFact
	NotExist_St_Facts map[string]map[string][]KnownSpecFact_InUniSpecFact
}

func NewSpecFactInUniFactMem() *SpecFactInUniFactMem {
	return &SpecFactInUniFactMem{
		PureFacts:         map[string]map[string][]KnownSpecFact_InUniSpecFact{},
		NotPureFacts:      map[string]map[string][]KnownSpecFact_InUniSpecFact{},
		ExistFacts:        map[string]map[string][]KnownSpecFact_InUniSpecFact{},
		NotExistFacts:     map[string]map[string][]KnownSpecFact_InUniSpecFact{},
		Exist_St_Facts:    map[string]map[string][]KnownSpecFact_InUniSpecFact{},
		NotExist_St_Facts: map[string]map[string][]KnownSpecFact_InUniSpecFact{},
	}
}

func (s SpecFactInUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string]map[string][]KnownSpecFact_InUniSpecFact, error) {
	switch stmt.TypeEnum {
	case ast.TrueAtom:
		return s.PureFacts, nil
	case ast.FalseAtom:
		return s.NotPureFacts, nil
	case ast.TrueExist:
		return s.ExistFacts, nil
	case ast.FalseExist:
		return s.NotExistFacts, nil
	case ast.TrueExist_St:
		return s.Exist_St_Facts, nil
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, nil
	default:
		return nil, errors.New("invalid spec fact type")
	}
}

func (s SpecFactInUniFactMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]KnownSpecFact_InUniSpecFact, bool) {
	sameEnumFacts, err := s.getSameEnumFacts(stmt)
	if err != nil {
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

func (s SpecFactInUniFactMem) NewFact(stmt *ast.UniFactStmt) error {
	for _, thenStmt := range stmt.ThenFacts {
		if stmtAsSpecFact, ok := thenStmt.(*ast.SpecFactStmt); ok {
			if stmtAsSpecFact.IsSpecFactNameWithUniPrefix() {
				return fmt.Errorf("facts in the body of universal fact should not be a free fact, got %s", stmtAsSpecFact.String())
			}

			err := s.insertSpecFact(stmtAsSpecFact, stmt)
			if err != nil {
				return err
			}

		} else if thenStmtAsConUniFact, ok := thenStmt.(*ast.UniFactStmt); ok {
			err := s.mergeOuterInnerUniFactAndInsert(thenStmtAsConUniFact, stmt)
			if err != nil {
				return err
			}
		} else {
			return fmt.Errorf("TODO: Currently only support spec fact in uni fact, but got: %s", thenStmt.String())
		}
	}
	return nil
}

func (s SpecFactInUniFactMem) insertSpecFact(stmtAsSpecFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt) error {
	sameEnumFacts, err := s.getSameEnumFacts(stmtAsSpecFact)
	if err != nil {
		return err
	}

	if _, ok := sameEnumFacts[stmtAsSpecFact.PropName.PkgName]; !ok {
		sameEnumFacts[stmtAsSpecFact.PropName.PkgName] = make(map[string][]KnownSpecFact_InUniSpecFact)
	}
	if _, ok := sameEnumFacts[stmtAsSpecFact.PropName.PkgName][stmtAsSpecFact.PropName.Name]; !ok {
		sameEnumFacts[stmtAsSpecFact.PropName.PkgName][stmtAsSpecFact.PropName.Name] = []KnownSpecFact_InUniSpecFact{}
	}

	sameEnumFacts[stmtAsSpecFact.PropName.PkgName][stmtAsSpecFact.PropName.Name] = append(sameEnumFacts[stmtAsSpecFact.PropName.PkgName][stmtAsSpecFact.PropName.Name], KnownSpecFact_InUniSpecFact{stmtAsSpecFact, uniFact})

	return nil
}
