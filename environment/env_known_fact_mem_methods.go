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
	glob "golitex/glob"
)

func (s SpecFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (glob.Map2D[[]KnownSpecFact], error) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, nil
	case ast.FalsePure:
		return s.NotPureFacts, nil
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
	// TODO 这里的 nil 要改成 env.CurSupposeMatchEnv
	sameEnumFacts[stmt.PropName.PkgName][stmt.PropName.Name] = append(sameEnumFacts[stmt.PropName.PkgName][stmt.PropName.Name], KnownSpecFact{stmt, nil})

	return nil
}

func (s SpecFactInLogicExprMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (glob.Map2D[[]KnownSpecFact_InLogicExpr], error) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, nil
	case ast.FalsePure:
		return s.NotPureFacts, nil
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

		sameEnumFacts[pair.Stmt.PropName.PkgName][pair.Stmt.PropName.Name] = append(sameEnumFacts[pair.Stmt.PropName.PkgName][pair.Stmt.PropName.Name], KnownSpecFact_InLogicExpr{pair.Stmt, pair.Indexes, logicExpr, nil})
	}

	return nil
}

func (s SpecFactInUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (glob.Map2D[[]KnownSpecFact_InUniSpecFact], error) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, nil
	case ast.FalsePure:
		return s.NotPureFacts, nil
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

			err := env.KnownFacts.SpecFactInUniFactMem.insertSpecFact(stmtAsSpecFact, stmt, nil)
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

			err := env.KnownFacts.SpecFact_InLogicExpr_InUniFactMem.NewFact(stmt, thenStmtAsLogicExpr, nil)
			if err != nil {
				return err
			}
		} else {
			return fmt.Errorf("TODO: newSpecFactInUniFact Currently only support spec fact in uni fact, but got: %s", thenStmt.String())
		}
	}
	return nil

}

func (s SpecFactInUniFactMem) insertSpecFact(stmtAsSpecFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt, envFact *ast.SpecFactStmt) error {
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

	sameEnumFacts[stmtAsSpecFact.PropName.PkgName][stmtAsSpecFact.PropName.Name] = append(sameEnumFacts[stmtAsSpecFact.PropName.PkgName][stmtAsSpecFact.PropName.Name], KnownSpecFact_InUniSpecFact{stmtAsSpecFact, uniFact, envFact})

	return nil
}

func (s SpecFact_InLogicExpr_InUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (glob.Map2D[[]SpecFact_InLogicExpr_InUniFact], error) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, nil
	case ast.FalsePure:
		return s.NotPureFacts, nil
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

func (s SpecFact_InLogicExpr_InUniFactMem) NewFact(uniStmt *ast.UniFactStmt, logicExpr *ast.LogicExprStmt, envFact *ast.SpecFactStmt) error {
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

		sameEnumFacts[pair.Stmt.PropName.PkgName][pair.Stmt.PropName.Name] = append(sameEnumFacts[pair.Stmt.PropName.PkgName][pair.Stmt.PropName.Name], SpecFact_InLogicExpr_InUniFact{pair.Stmt, uniStmt, pair.Indexes, logicExpr, envFact})
	}

	return nil
}

func newSpecFact_InLogicExpr_InUniFactMem() *SpecFact_InLogicExpr_InUniFactMem {
	return &SpecFact_InLogicExpr_InUniFactMem{
		PureFacts:         make(glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]),
		NotPureFacts:      make(glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]),
		Exist_St_Facts:    make(glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]),
		NotExist_St_Facts: make(glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]),
	}
}

func (e *Env) GetSpecFactMem(envFact *ast.SpecFactStmt) (*SpecFactMem, bool) {
	if envFact != nil {
		knownFacts, ok := e.GetFactsFromKnownFactInMatchEnv(envFact)
		if !ok {
			return nil, false
		}
		return &knownFacts.SpecFactMem, true
	}
	return &e.KnownFacts.SpecFactMem, true
}

func (e *Env) GetSpecFactInLogicExprMem(envFact *ast.SpecFactStmt) (*SpecFactInLogicExprMem, bool) {
	if envFact != nil {
		knownFacts, ok := e.GetFactsFromKnownFactInMatchEnv(envFact)
		if !ok {
			return nil, false
		}
		return &knownFacts.SpecFactInLogicExprMem, true
	}
	return &e.KnownFacts.SpecFactInLogicExprMem, true
}

func (e *Env) GetSpecFactInUniFactMem(envFact *ast.SpecFactStmt) (*SpecFactInUniFactMem, bool) {
	if envFact != nil {
		knownFacts, ok := e.GetFactsFromKnownFactInMatchEnv(envFact)
		if !ok {
			return nil, false
		}
		return &knownFacts.SpecFactInUniFactMem, true
	}
	return &e.KnownFacts.SpecFactInUniFactMem, true
}

func (e *Env) GetSpecFact_InLogicExpr_InUniFactMem(envFact *ast.SpecFactStmt) (*SpecFact_InLogicExpr_InUniFactMem, bool) {
	if envFact != nil {
		knownFacts, ok := e.GetFactsFromKnownFactInMatchEnv(envFact)
		if !ok {
			return nil, false
		}
		return &knownFacts.SpecFact_InLogicExpr_InUniFactMem, true
	}
	return &e.KnownFacts.SpecFact_InLogicExpr_InUniFactMem, true
}
