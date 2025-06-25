// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

import (
	"errors"
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

// func (s SpecFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (glob.Map2D[[]KnownSpecFact], error) {
func (s SpecFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]KnownSpecFact, error) {
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

	// sameEnumPkgFacts, memExist := sameEnumFacts[stmt.PropName.PkgName]
	// 	if !memExist {
	// 		return nil, false
	// }

	// sameEnumPkgPropFacts, memExist := sameEnumPkgFacts[stmt.PropName.Name]
	sameEnumPkgPropFacts, memExist := sameEnumFacts[stmt.PropName.Name]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFactMem) newFact(stmt *ast.SpecFactStmt, supposedEnv *ast.SpecFactStmt) error {
	// 要考虑pkgName和propName是否存在
	sameEnumFacts, err := s.getSameEnumFacts(stmt)
	if err != nil {
		return err
	}

	// if _, ok := sameEnumFacts[stmt.PropName.PkgName]; !ok {
	// 	sameEnumFacts[stmt.PropName.PkgName] = make(map[string][]KnownSpecFact)
	// }
	// if _, ok := sameEnumFacts[stmt.PropName.PkgName][stmt.PropName.Name]; !ok {
	// 	sameEnumFacts[stmt.PropName.PkgName][stmt.PropName.Name] = []KnownSpecFact{}
	// }
	// sameEnumFacts[stmt.PropName.PkgName][stmt.PropName.Name] = append(sameEnumFacts[stmt.PropName.PkgName][stmt.PropName.Name], KnownSpecFact{stmt, supposedEnv})

	if _, ok := sameEnumFacts[stmt.PropName.Name]; !ok {
		sameEnumFacts[stmt.PropName.Name] = []KnownSpecFact{}
	}
	sameEnumFacts[stmt.PropName.Name] = append(sameEnumFacts[stmt.PropName.Name], KnownSpecFact{stmt, supposedEnv})

	return nil
}

// func (s SpecFactInLogicExprMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (glob.Map2D[[]KnownSpecFact_InLogicExpr], error) {
func (s SpecFactInLogicExprMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]KnownSpecFact_InLogicExpr, error) {
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

	// sameEnumPkgFacts, memExist := sameEnumFacts[stmt.PropName.PkgName]
	// if !memExist {
	// 	return nil, false
	// }

	// sameEnumPkgPropFacts, memExist := sameEnumPkgFacts[stmt.PropName.Name]
	sameEnumPkgPropFacts, memExist := sameEnumFacts[stmt.PropName.Name]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFactInLogicExprMem) newFact(logicExpr *ast.OrStmt, supposedEnv *ast.SpecFactStmt) error {
	for i, fact := range logicExpr.Facts {
		sameEnumFacts, err := s.getSameEnumFacts(&fact)
		if err != nil {
			return err
		}

		// if _, ok := sameEnumFacts[fact.PropName.PkgName]; !ok {
		// 	sameEnumFacts[fact.PropName.PkgName] = make(map[string][]KnownSpecFact_InLogicExpr)
		// }
		// if _, ok := sameEnumFacts[fact.PropName.PkgName][fact.PropName.Name]; !ok {
		// 	sameEnumFacts[fact.PropName.PkgName][fact.PropName.Name] = []KnownSpecFact_InLogicExpr{}
		// }
		// sameEnumFacts[fact.PropName.PkgName][fact.PropName.Name] = append(sameEnumFacts[fact.PropName.PkgName][fact.PropName.Name], *NewKnownSpecFact_InLogicExpr(&fact, i, logicExpr, supposedEnv))

		if _, ok := sameEnumFacts[fact.PropName.Name]; !ok {
			sameEnumFacts[fact.PropName.Name] = []KnownSpecFact_InLogicExpr{}
		}
		sameEnumFacts[fact.PropName.Name] = append(sameEnumFacts[fact.PropName.Name], *NewKnownSpecFact_InLogicExpr(&fact, i, logicExpr, supposedEnv))
	}

	return nil
}

// func (s SpecFactInUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (glob.Map2D[[]KnownSpecFact_InUniFact], error) {
func (s SpecFactInUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]KnownSpecFact_InUniFact, error) {
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

func (s SpecFactInUniFactMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]KnownSpecFact_InUniFact, bool) {
	sameEnumFacts, err := s.getSameEnumFacts(stmt)
	if err != nil {
		return nil, false
	}

	// sameEnumPkgFacts, memExist := sameEnumFacts[stmt.PropName.PkgName]
	// if !memExist {
	// 	return nil, false
	// }

	// sameEnumPkgPropFacts, memExist := sameEnumPkgFacts[stmt.PropName.Name]
	sameEnumPkgPropFacts, memExist := sameEnumFacts[stmt.PropName.Name]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (env *Env) newUniFact(stmt *ast.UniFactStmt) error {
	for _, thenStmt := range stmt.ThenFacts {
		if stmtAsSpecFact, ok := thenStmt.(*ast.SpecFactStmt); ok {
			err := env.storeUniFact(stmtAsSpecFact, stmt)
			if err != nil {
				return err
			}
		} else if thenStmtAsUniFact, ok := thenStmt.(*ast.UniFactStmt); ok {
			mergedUniFact := ast.MergeOuterInnerUniFacts(stmt, thenStmtAsUniFact)
			err := env.newUniFact(mergedUniFact)
			if err != nil {
				return err
			}
		} else if thenStmtAsLogicExpr, ok := thenStmt.(*ast.OrStmt); ok {
			err := env.KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem.NewFact(stmt, thenStmtAsLogicExpr, env.CurMatchProp)
			if err != nil {
				return err
			}
		} else {
			return fmt.Errorf("TODO: newSpecFactInUniFact Currently only support spec fact in uni fact, but got: %s", thenStmt.String())
		}
	}
	return nil

}

func (s SpecFactInUniFactMem) newFact(stmtAsSpecFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt, supposedEnv *ast.SpecFactStmt) error {
	sameEnumFacts, err := s.getSameEnumFacts(stmtAsSpecFact)
	if err != nil {
		return err
	}

	// if _, ok := sameEnumFacts[stmtAsSpecFact.PropName.PkgName]; !ok {
	// 	sameEnumFacts[stmtAsSpecFact.PropName.PkgName] = make(map[string][]KnownSpecFact_InUniFact)
	// }
	// if _, ok := sameEnumFacts[stmtAsSpecFact.PropName.PkgName][stmtAsSpecFact.PropName.Name]; !ok {
	// 	sameEnumFacts[stmtAsSpecFact.PropName.PkgName][stmtAsSpecFact.PropName.Name] = []KnownSpecFact_InUniFact{}
	// }

	// sameEnumFacts[stmtAsSpecFact.PropName.PkgName][stmtAsSpecFact.PropName.Name] = append(sameEnumFacts[stmtAsSpecFact.PropName.PkgName][stmtAsSpecFact.PropName.Name], KnownSpecFact_InUniFact{stmtAsSpecFact, uniFact, supposedEnv})
	if _, ok := sameEnumFacts[stmtAsSpecFact.PropName.Name]; !ok {
		sameEnumFacts[stmtAsSpecFact.PropName.Name] = []KnownSpecFact_InUniFact{}
	}
	sameEnumFacts[stmtAsSpecFact.PropName.Name] = append(sameEnumFacts[stmtAsSpecFact.PropName.Name], KnownSpecFact_InUniFact{stmtAsSpecFact, uniFact, supposedEnv})

	return nil
}

// func (s SpecFact_InLogicExpr_InUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (glob.Map2D[[]SpecFact_InLogicExpr_InUniFact], error) {
func (s SpecFact_InLogicExpr_InUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]SpecFact_InLogicExpr_InUniFact, error) {
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

	// sameEnumPkgFacts, memExist := sameEnumFacts[stmt.PropName.PkgName]
	// if !memExist {
	// 	return nil, false
	// }

	// sameEnumPkgPropFacts, memExist := sameEnumPkgFacts[stmt.PropName.Name]
	sameEnumPkgPropFacts, memExist := sameEnumFacts[stmt.PropName.Name]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFact_InLogicExpr_InUniFactMem) NewFact(uniStmt *ast.UniFactStmt, logicExpr *ast.OrStmt, supposedEnv *ast.SpecFactStmt) error {
	for i, fact := range logicExpr.Facts {
		sameEnumFacts, err := s.getSameEnumFacts(&fact)
		if err != nil {
			return err
		}

		// if _, ok := sameEnumFacts[fact.PropName.PkgName]; !ok {
		// 	sameEnumFacts[fact.PropName.PkgName] = make(map[string][]SpecFact_InLogicExpr_InUniFact)
		// }
		// if _, ok := sameEnumFacts[fact.PropName.PkgName][fact.PropName.Name]; !ok {
		// 	sameEnumFacts[fact.PropName.PkgName][fact.PropName.Name] = []SpecFact_InLogicExpr_InUniFact{}
		// }

		// sameEnumFacts[fact.PropName.PkgName][fact.PropName.Name] = append(sameEnumFacts[fact.PropName.PkgName][fact.PropName.Name], *NewSpecFact_InLogicExpr_InUniFact(&fact, uniStmt, i, logicExpr, supposedEnv))

		if _, ok := sameEnumFacts[fact.PropName.Name]; !ok {
			sameEnumFacts[fact.PropName.Name] = []SpecFact_InLogicExpr_InUniFact{}
		}
		sameEnumFacts[fact.PropName.Name] = append(sameEnumFacts[fact.PropName.Name], *NewSpecFact_InLogicExpr_InUniFact(&fact, uniStmt, i, logicExpr, supposedEnv))
	}

	return nil
}

func newSpecFact_InLogicExpr_InUniFactMem() *SpecFact_InLogicExpr_InUniFactMem {
	return &SpecFact_InLogicExpr_InUniFactMem{
		// PureFacts:         make(glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]),
		// NotPureFacts:      make(glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]),
		// Exist_St_Facts:    make(glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]),
		// NotExist_St_Facts: make(glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]),
		PureFacts:         make(map[string][]SpecFact_InLogicExpr_InUniFact),
		NotPureFacts:      make(map[string][]SpecFact_InLogicExpr_InUniFact),
		Exist_St_Facts:    make(map[string][]SpecFact_InLogicExpr_InUniFact),
		NotExist_St_Facts: make(map[string][]SpecFact_InLogicExpr_InUniFact),
	}
}

func (e *Env) GetSpecFactMem() (*SpecFactMem, bool) {
	if e.CurMatchProp != nil {
		knownFacts, ok := e.GetFactsFromKnownFactInMatchEnv(e.CurMatchProp)
		if !ok {
			return nil, false
		}
		return &knownFacts.SpecFactMem, true
	}
	return &e.KnownFactsStruct.SpecFactMem, true
}

func (e *Env) GetSpecFactInLogicExprMem() (*SpecFactInLogicExprMem, bool) {
	if e.CurMatchProp != nil {
		knownFacts, ok := e.GetFactsFromKnownFactInMatchEnv(e.CurMatchProp)
		if !ok {
			return nil, false
		}
		return &knownFacts.SpecFactInLogicExprMem, true
	}
	return &e.KnownFactsStruct.SpecFactInLogicExprMem, true
}

func (e *Env) GetSpecFactInUniFactMem() (*SpecFactInUniFactMem, bool) {
	if e.CurMatchProp != nil {
		knownFacts, ok := e.GetFactsFromKnownFactInMatchEnv(e.CurMatchProp)
		if !ok {
			return nil, false
		}
		return &knownFacts.SpecFactInUniFactMem, true
	}
	return &e.KnownFactsStruct.SpecFactInUniFactMem, true
}

func (e *Env) GetSpecFact_InLogicExpr_InUniFactMem() (*SpecFact_InLogicExpr_InUniFactMem, bool) {
	if e.CurMatchProp != nil {
		knownFacts, ok := e.GetFactsFromKnownFactInMatchEnv(e.CurMatchProp)
		if !ok {
			return nil, false
		}
		return &knownFacts.SpecFact_InLogicExpr_InUniFactMem, true
	}
	return &e.KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem, true
}

func (e *Env) IsFnDeclared(fc ast.FcAtom) (*ast.FnTemplateStmt, bool) {
	// TODO 这里需要更严格检查一下是否是正常的函数名
	if _, ok := glob.BuiltinKeywordsSet[fc.Name]; ok {
		return nil, true
	}

	// TODO 这里需要更严格检查一下是否是正常的函数名
	if glob.IsKeySymbol(fc.Name) {
		return nil, true
	}

	fnDef, ok := e.GetLatestFnTemplate(fc)
	if !ok {
		return nil, false
	}
	return fnDef, true
}

func (e *Env) newUniFactWithIff(stmt *ast.UniFactWithIffStmt) error {
	thenToIff := stmt.NewUniFactWithThenToIff()
	err := e.newUniFact(thenToIff)
	if err != nil {
		return err
	}

	iffToThen := stmt.NewUniFactWithIffToThen()
	err = e.newUniFact(iffToThen)
	if err != nil {
		return err
	}

	return nil
}

func (e *Env) StoreFnSatisfyFnTemplateFact(fn ast.Fc, fnTemplate *ast.FnTemplateStmt) error {
	err := e.FnInFnTemplateFactsMem.insert(fn, fnTemplate)
	if err != nil {
		return err
	}

	return nil
}
