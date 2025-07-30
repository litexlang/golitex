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

func (s SpecFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]ast.SpecFactStmt, error) {
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

func (s SpecFactMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]ast.SpecFactStmt, bool) {
	sameEnumFacts, err := s.getSameEnumFacts(stmt)
	if err != nil {
		return nil, false
	}

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.PropName)]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFactMem) newFact(stmt *ast.SpecFactStmt) error {
	// 要考虑pkgName和propName是否存在
	sameEnumFacts, err := s.getSameEnumFacts(stmt)
	if err != nil {
		return err
	}

	if _, ok := sameEnumFacts[string(stmt.PropName)]; !ok {
		sameEnumFacts[string(stmt.PropName)] = []ast.SpecFactStmt{}
	}
	sameEnumFacts[string(stmt.PropName)] = append(sameEnumFacts[string(stmt.PropName)], *stmt)
	return nil
}

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

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.PropName)]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFactInLogicExprMem) newFact(logicExpr *ast.OrStmt) error {
	for i, fact := range logicExpr.Facts {
		sameEnumFacts, err := s.getSameEnumFacts(fact)
		if err != nil {
			return err
		}

		if _, ok := sameEnumFacts[string(fact.PropName)]; !ok {
			sameEnumFacts[string(fact.PropName)] = []KnownSpecFact_InLogicExpr{}
		}
		sameEnumFacts[string(fact.PropName)] = append(sameEnumFacts[string(fact.PropName)], *NewKnownSpecFact_InLogicExpr(fact, i, logicExpr))
	}

	return nil
}

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

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.PropName)]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (env *Env) newUniFact(stmt *ast.UniFactStmt) error {
	for _, thenStmt := range stmt.ThenFacts {
		var err error
		switch asFact := thenStmt.(type) {
		case *ast.SpecFactStmt:
			err = env.newUniFact_ThenFactIsSpecFact(stmt, asFact)
		case *ast.OrStmt:
			err = env.newUniFact_ThenFactIsOrStmt(stmt, asFact)
		case *ast.EnumStmt:
			err = env.newUniFact_ThenFactIsEnumStmt(stmt, asFact)
		case *ast.IntensionalSetStmt:
			err = env.newUniFact_ThenFactIsIntensionalSetStmt(stmt, asFact)
		case *ast.UniFactWithIffStmt:
			err = env.newUniFact_ThenFactIsIffStmt(stmt, asFact)
		case *ast.UniFactStmt:
			err = env.newUniFact_ThenFactIsUniFactStmt(stmt, asFact)
		case *ast.EqualsFactStmt:
			err = env.newUniFact_ThenFactIsEqualsFactStmt(stmt, asFact)
		default:
			return fmt.Errorf("invalid then fact type: %s", thenStmt)
		}

		if err != nil {
			return err
		}
	}
	return nil

}

func (s SpecFactInUniFactMem) newFact(stmtAsSpecFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt) error {
	sameEnumFacts, err := s.getSameEnumFacts(stmtAsSpecFact)
	if err != nil {
		return err
	}

	if _, ok := sameEnumFacts[string(stmtAsSpecFact.PropName)]; !ok {
		sameEnumFacts[string(stmtAsSpecFact.PropName)] = []KnownSpecFact_InUniFact{}
	}
	sameEnumFacts[string(stmtAsSpecFact.PropName)] = append(sameEnumFacts[string(stmtAsSpecFact.PropName)], KnownSpecFact_InUniFact{stmtAsSpecFact, uniFact})

	return nil
}

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

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.PropName)]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFact_InLogicExpr_InUniFactMem) NewFact(uniStmt *ast.UniFactStmt, logicExpr *ast.OrStmt) error {
	for i, fact := range logicExpr.Facts {
		sameEnumFacts, err := s.getSameEnumFacts(fact)
		if err != nil {
			return err
		}

		if _, ok := sameEnumFacts[string(fact.PropName)]; !ok {
			sameEnumFacts[string(fact.PropName)] = []SpecFact_InLogicExpr_InUniFact{}
		}
		sameEnumFacts[string(fact.PropName)] = append(sameEnumFacts[string(fact.PropName)], *NewSpecFact_InLogicExpr_InUniFact(fact, uniStmt, i, logicExpr))
	}

	return nil
}

func newSpecFact_InLogicExpr_InUniFactMem() *SpecFact_InLogicExpr_InUniFactMem {
	return &SpecFact_InLogicExpr_InUniFactMem{
		PureFacts:         make(map[string][]SpecFact_InLogicExpr_InUniFact),
		NotPureFacts:      make(map[string][]SpecFact_InLogicExpr_InUniFact),
		Exist_St_Facts:    make(map[string][]SpecFact_InLogicExpr_InUniFact),
		NotExist_St_Facts: make(map[string][]SpecFact_InLogicExpr_InUniFact),
	}
}

func (e *Env) GetSpecFactMem() (*SpecFactMem, bool) {
	return &e.KnownFactsStruct.SpecFactMem, true
}

func (e *Env) GetSpecFactInLogicExprMem() (*SpecFactInLogicExprMem, bool) {
	return &e.KnownFactsStruct.SpecFactInLogicExprMem, true
}

func (e *Env) GetSpecFactInUniFactMem() (*SpecFactInUniFactMem, bool) {
	return &e.KnownFactsStruct.SpecFactInUniFactMem, true
}

func (e *Env) GetSpecFact_InLogicExpr_InUniFactMem() (*SpecFact_InLogicExpr_InUniFactMem, bool) {
	return &e.KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem, true
}

func (e *Env) IsFnDeclared(fc ast.FcAtom) (*FnInFnTTMemItem, bool) {
	// TODO 这里需要更严格检查一下是否是正常的函数名，但是目前没有
	if _, ok := glob.BuiltinKeywordsSet[string(fc)]; ok {
		return nil, true
	}

	// TODO 这里需要更严格检查一下是否是正常的函数名
	if glob.IsKeySymbol(string(fc)) {
		return nil, true
	}

	fnDef, ok := e.GetLatestFnTT_GivenNameIsIn(string(fc))
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

func (e *Env) StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(fn ast.Fc, fnTemplateFcFn *ast.FcFn, fnTNoName *ast.FnTStruct) error {
	err := e.InsertFnInFnTT(fn, fnTemplateFcFn, fnTNoName)
	if err != nil {
		return err
	}

	return nil
}

func (e *Env) StoreFnSatisfyFnTemplateFact(fn ast.Fc, fnTemplateFcFn *ast.FcFn) error {
	fnTNoName, ok, err := e.getInstantiatedFnTTOfFcFn(fnTemplateFcFn)
	if err != nil || !ok {
		return err
	}

	err = e.InsertFnInFnTT(fn, fnTemplateFcFn, fnTNoName)
	if err != nil {
		return err
	}

	return nil
}

func (e *Env) getInstantiatedFnTTOfFcFn(fcFn *ast.FcFn) (*ast.FnTStruct, bool, error) {
	if ast.IsFnFcFn(fcFn) {
		fnTNoName, err := fcFn.FnTFc_ToFnTNoName()
		if err != nil {
			return nil, false, err
		}
		return fnTNoName, true, nil
	}

	def, ok := e.GetFnTemplateDef(fcFn.FnHead.(ast.FcAtom))
	if !ok {
		return nil, false, nil
	}

	fnTNoName, err := def.Instantiate_GetFnTemplateNoName(fcFn)
	if err != nil {
		return nil, false, err
	}

	return fnTNoName, true, nil
}
