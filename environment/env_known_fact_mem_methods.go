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
	ast "golitex/ast"
)

func newSpecFactMem() *SpecFactMem {
	return &SpecFactMem{
		PureFacts:    map[string]map[string][]KnownSpecFact{},
		NotPureFacts: map[string]map[string][]KnownSpecFact{},
		// ExistFacts:        map[string]map[string][]KnownSpecFact{},
		// NotExistFacts:     map[string]map[string][]KnownSpecFact{},
		Exist_St_Facts:    map[string]map[string][]KnownSpecFact{},
		NotExist_St_Facts: map[string]map[string][]KnownSpecFact{},
	}
}

func NewSpecFactInLogicExprMem() *SpecFactInLogicExprMem {
	return &SpecFactInLogicExprMem{
		PureFacts:    map[string]map[string][]KnownSpecFact_InLogicExpr{},
		NotPureFacts: map[string]map[string][]KnownSpecFact_InLogicExpr{},
		// ExistFacts:        map[string]map[string][]KnownSpecFact_InLogicExpr{},
		// NotExistFacts:     map[string]map[string][]KnownSpecFact_InLogicExpr{},
		Exist_St_Facts:    map[string]map[string][]KnownSpecFact_InLogicExpr{},
		NotExist_St_Facts: map[string]map[string][]KnownSpecFact_InLogicExpr{},
	}
}

func NewSpecFactInUniFact() *SpecFactInUniFactMem {
	return &SpecFactInUniFactMem{
		PureFacts:    map[string]map[string][]KnownSpecFact_InUniSpecFact{},
		NotPureFacts: map[string]map[string][]KnownSpecFact_InUniSpecFact{},
		// ExistFacts:        map[string]map[string][]KnownSpecFact_InUniSpecFact{},
		// NotExistFacts:     map[string]map[string][]KnownSpecFact_InUniSpecFact{},
		Exist_St_Facts:    map[string]map[string][]KnownSpecFact_InUniSpecFact{},
		NotExist_St_Facts: map[string]map[string][]KnownSpecFact_InUniSpecFact{},
	}
}

func NewKnownSpecFact_InLogicExpr_InUniFactMem() *SpecFact_InLogicExpr_InUniFactMem {
	return &SpecFact_InLogicExpr_InUniFactMem{
		PureFacts:    map[string]map[string][]SpecFact_InLogicExpr_InUniFact{},
		NotPureFacts: map[string]map[string][]SpecFact_InLogicExpr_InUniFact{},
		// ExistFacts:        map[string]map[string][]SpecFact_InLogicExpr_InUniFact{},
		// NotExistFacts:     map[string]map[string][]SpecFact_InLogicExpr_InUniFact{},
		Exist_St_Facts:    map[string]map[string][]SpecFact_InLogicExpr_InUniFact{},
		NotExist_St_Facts: map[string]map[string][]SpecFact_InLogicExpr_InUniFact{},
	}
}

func (s SpecFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string]map[string][]KnownSpecFact, error) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, nil
	case ast.FalsePure:
		return s.NotPureFacts, nil
	// case ast.TrueExist:
	// 	return s.ExistFacts, nil
	// case ast.FalseExist:
	// 	return s.NotExistFacts, nil
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

func (s SpecFactInLogicExprMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string]map[string][]KnownSpecFact_InLogicExpr, error) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, nil
	case ast.FalsePure:
		return s.NotPureFacts, nil
	// case ast.TrueExist:
	// 	return s.ExistFacts, nil
	// case ast.FalseExist:
	// 	return s.NotExistFacts, nil
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

func (s SpecFactInUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string]map[string][]KnownSpecFact_InUniSpecFact, error) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, nil
	case ast.FalsePure:
		return s.NotPureFacts, nil
	// case ast.TrueExist:
	// 	return s.ExistFacts, nil
	// case ast.FalseExist:
	// 	return s.NotExistFacts, nil
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

func (env *Env) storeUniFact(stmt *ast.UniFactStmt) error {
	for _, thenStmt := range stmt.ThenFacts {
		if stmtAsSpecFact, ok := thenStmt.(*ast.SpecFactStmt); ok {
			if stmtAsSpecFact.IsSpecFactNameWithUniPrefix() {
				return fmt.Errorf("facts in the body of universal fact should not be a free fact, got %s", stmtAsSpecFact.String())
			}

			err := env.SpecFactInUniFactMem.insertSpecFact(stmtAsSpecFact, stmt)
			if err != nil {
				return err
			}

		} else if thenStmtAsUniFact, ok := thenStmt.(*ast.UniFactStmt); ok {
			mergedUniFact := ast.MergeOuterInnerUniFacts(stmt, thenStmtAsUniFact)

			err := env.storeUniFact(mergedUniFact)
			if err != nil {
				return err
			}
		} else if thenStmtAsLogicExpr, ok := thenStmt.(*ast.LogicExprStmt); ok {

			if thenStmtAsLogicExpr.IsSpecFactNameWithUniPrefix() {
				return fmt.Errorf("facts in the body of universal fact should not be a free fact, got %s", thenStmtAsLogicExpr.String())
			}

			err := env.SpecFact_InLogicExpr_InUniFactMem.NewFact(stmt, thenStmtAsLogicExpr)
			if err != nil {
				return err
			}
		} else {
			return fmt.Errorf("TODO: newSpecFactInUniFact Currently only support spec fact in uni fact, but got: %s", thenStmt.String())
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

func (s SpecFact_InLogicExpr_InUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string]map[string][]SpecFact_InLogicExpr_InUniFact, error) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, nil
	case ast.FalsePure:
		return s.NotPureFacts, nil
	// case ast.TrueExist:
	// 	return s.ExistFacts, nil
	// case ast.FalseExist:
	// 	return s.NotExistFacts, nil
	case ast.TrueExist_St:
		return s.Exist_St_Facts, nil
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, nil
	default:
		return nil, errors.New("invalid spec fact type")
	}
}

func (s SpecFact_InLogicExpr_InUniFactMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]SpecFact_InLogicExpr_InUniFact, bool) {
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

func (s SpecFact_InLogicExpr_InUniFactMem) NewFact(uniStmt *ast.UniFactStmt, logicExpr *ast.LogicExprStmt) error {
	pair, err := logicExpr.SpecFactIndexPairs([]uint8{})
	if err != nil {
		return err
	}

	for _, pair := range pair {
		sameEnumFacts, err := s.getSameEnumFacts(pair.Stmt)
		if err != nil {
			return err
		}

		if _, ok := sameEnumFacts[pair.Stmt.PropName.PkgName]; !ok {
			sameEnumFacts[pair.Stmt.PropName.PkgName] = make(map[string][]SpecFact_InLogicExpr_InUniFact)
		}
		if _, ok := sameEnumFacts[pair.Stmt.PropName.PkgName][pair.Stmt.PropName.Name]; !ok {
			sameEnumFacts[pair.Stmt.PropName.PkgName][pair.Stmt.PropName.Name] = []SpecFact_InLogicExpr_InUniFact{}
		}

		sameEnumFacts[pair.Stmt.PropName.PkgName][pair.Stmt.PropName.Name] = append(sameEnumFacts[pair.Stmt.PropName.PkgName][pair.Stmt.PropName.Name], SpecFact_InLogicExpr_InUniFact{pair.Stmt, uniStmt, pair.Indexes, logicExpr})
	}

	return nil
}

func NewSpecFact_InLogicExpr_InUniFactMem() *SpecFact_InLogicExpr_InUniFactMem {
	return &SpecFact_InLogicExpr_InUniFactMem{
		PureFacts:         map[string]map[string][]SpecFact_InLogicExpr_InUniFact{},
		NotPureFacts:      map[string]map[string][]SpecFact_InLogicExpr_InUniFact{},
		ExistFacts:        map[string]map[string][]SpecFact_InLogicExpr_InUniFact{},
		NotExistFacts:     map[string]map[string][]SpecFact_InLogicExpr_InUniFact{},
		Exist_St_Facts:    map[string]map[string][]SpecFact_InLogicExpr_InUniFact{},
		NotExist_St_Facts: map[string]map[string][]SpecFact_InLogicExpr_InUniFact{},
	}
}
