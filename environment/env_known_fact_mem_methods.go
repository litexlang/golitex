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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

import (
	"errors"
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (s SpecFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]ast.SpecFactStmt, glob.GlobRet) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, glob.TrueRet("")
	case ast.FalsePure:
		return s.NotPureFacts, glob.TrueRet("")
	case ast.TrueExist_St:
		return s.Exist_St_Facts, glob.TrueRet("")
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, glob.TrueRet("")
	default:
		return nil, glob.ErrRet(errors.New("invalid spec fact type"))
	}
}

func (s SpecFactMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]ast.SpecFactStmt, bool) {
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return nil, false
	}

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.PropName)]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFactMem) newFact(stmt *ast.SpecFactStmt) glob.GlobRet {
	// 要考虑pkgName和propName是否存在
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return ret
	}

	if _, ok := sameEnumFacts[string(stmt.PropName)]; !ok {
		sameEnumFacts[string(stmt.PropName)] = []ast.SpecFactStmt{}
	}
	sameEnumFacts[string(stmt.PropName)] = append(sameEnumFacts[string(stmt.PropName)], *stmt)
	return glob.TrueRet("")
}

func (s SpecFactInLogicExprMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]KnownSpecFact_InLogicExpr, glob.GlobRet) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, glob.TrueRet("")
	case ast.FalsePure:
		return s.NotPureFacts, glob.TrueRet("")
	case ast.TrueExist_St:
		return s.Exist_St_Facts, glob.TrueRet("")
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, glob.TrueRet("")
	default:
		return nil, glob.ErrRet(errors.New("invalid spec fact type"))
	}
}

func (s SpecFactInLogicExprMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]KnownSpecFact_InLogicExpr, bool) {
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return nil, false
	}

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.PropName)]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFactInLogicExprMem) newFact(logicExpr *ast.OrStmt) glob.GlobRet {
	for i, fact := range logicExpr.Facts {
		sameEnumFacts, ret := s.getSameEnumFacts(fact)
		if ret.IsErr() {
			return ret
		}

		if _, ok := sameEnumFacts[string(fact.PropName)]; !ok {
			sameEnumFacts[string(fact.PropName)] = []KnownSpecFact_InLogicExpr{}
		}
		sameEnumFacts[string(fact.PropName)] = append(sameEnumFacts[string(fact.PropName)], *NewKnownSpecFact_InLogicExpr(fact, i, logicExpr))
	}

	return glob.TrueRet("")
}

func (s SpecFactInUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]KnownSpecFact_InUniFact, glob.GlobRet) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, glob.TrueRet("")
	case ast.FalsePure:
		return s.NotPureFacts, glob.TrueRet("")
	case ast.TrueExist_St:
		return s.Exist_St_Facts, glob.TrueRet("")
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, glob.TrueRet("")
	default:
		return nil, glob.ErrRet(errors.New("invalid spec fact type"))
	}
}

func (s SpecFactInUniFactMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]KnownSpecFact_InUniFact, bool) {
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return nil, false
	}

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.PropName)]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (env *Env) newUniFact(stmt *ast.UniFactStmt) glob.GlobRet {
	for _, thenStmt := range stmt.ThenFacts {
		var ret glob.GlobRet
		switch asFact := thenStmt.(type) {
		case *ast.SpecFactStmt:
			ret = env.newUniFact_ThenFactIsSpecFact(stmt, asFact)
		case *ast.OrStmt:
			ret = env.newUniFact_ThenFactIsOrStmt(stmt, asFact)
		// case *ast.EnumStmt:
		// 	ret = env.newUniFact_ThenFactIsEnumStmt(stmt, asFact)
		// case *ast.IntensionalSetStmt:
		// 	ret = env.newUniFact_ThenFactIsIntensionalSetStmt(stmt, asFact)
		case *ast.UniFactWithIffStmt:
			ret = env.newUniFact_ThenFactIsIffStmt(stmt, asFact)
		case *ast.UniFactStmt:
			ret = env.newUniFact_ThenFactIsUniFactStmt(stmt, asFact)
		case *ast.EqualsFactStmt:
			ret = env.newUniFact_ThenFactIsEqualsFactStmt(stmt, asFact)
		default:
			return glob.ErrRet(fmt.Errorf("invalid then fact type: %s", thenStmt))
		}

		if ret.IsErr() {
			return ret
		}
	}
	return glob.TrueRet("")

}

func (s SpecFactInUniFactMem) newFact(stmtAsSpecFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt) glob.GlobRet {
	sameEnumFacts, ret := s.getSameEnumFacts(stmtAsSpecFact)
	if ret.IsErr() {
		return ret
	}

	if _, ok := sameEnumFacts[string(stmtAsSpecFact.PropName)]; !ok {
		sameEnumFacts[string(stmtAsSpecFact.PropName)] = []KnownSpecFact_InUniFact{}
	}
	sameEnumFacts[string(stmtAsSpecFact.PropName)] = append(sameEnumFacts[string(stmtAsSpecFact.PropName)], KnownSpecFact_InUniFact{stmtAsSpecFact, uniFact})

	return glob.TrueRet("")
}

func (s SpecFact_InLogicExpr_InUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]SpecFact_InLogicExpr_InUniFact, glob.GlobRet) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, glob.TrueRet("")
	case ast.FalsePure:
		return s.NotPureFacts, glob.TrueRet("")
	case ast.TrueExist_St:
		return s.Exist_St_Facts, glob.TrueRet("")
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, glob.TrueRet("")
	default:
		return nil, glob.ErrRet(errors.New("invalid spec fact type"))
	}
}

func (s SpecFact_InLogicExpr_InUniFactMem) GetSameEnumPkgPropFacts(stmt *ast.SpecFactStmt) ([]SpecFact_InLogicExpr_InUniFact, bool) {
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return nil, false
	}

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.PropName)]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFact_InLogicExpr_InUniFactMem) NewFact(uniStmt *ast.UniFactStmt, logicExpr *ast.OrStmt) glob.GlobRet {
	for i, fact := range logicExpr.Facts {
		sameEnumFacts, ret := s.getSameEnumFacts(fact)
		if ret.IsErr() {
			return ret
		}

		if _, ok := sameEnumFacts[string(fact.PropName)]; !ok {
			sameEnumFacts[string(fact.PropName)] = []SpecFact_InLogicExpr_InUniFact{}
		}
		sameEnumFacts[string(fact.PropName)] = append(sameEnumFacts[string(fact.PropName)], *NewSpecFact_InLogicExpr_InUniFact(fact, uniStmt, i, logicExpr))
	}

	return glob.TrueRet("")
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

func (e *Env) IsFnDeclared(fc ast.Atom) (*FnInFnTMemItem, bool) {
	// TODO 这里需要更严格检查一下是否是正常的函数名，但是目前没有
	if _, ok := glob.BuiltinKeywordsSet[string(fc)]; ok {
		return nil, true
	}

	// TODO 这里需要更严格检查一下是否是正常的函数名
	if glob.IsKeySymbol(string(fc)) {
		return nil, true
	}

	fnDef := e.GetLatestFnT_GivenNameIsIn(string(fc))
	if fnDef == nil {
		return nil, false
	}
	return fnDef, true
}

func (e *Env) newUniFactWithIff(stmt *ast.UniFactWithIffStmt) glob.GlobRet {
	thenToIff := stmt.NewUniFactWithThenToIff()
	ret := e.newUniFact(thenToIff)
	if ret.IsErr() {
		return ret
	}

	iffToThen := stmt.NewUniFactWithIffToThen()
	ret = e.newUniFact(iffToThen)
	if ret.IsErr() {
		return ret
	}

	return glob.TrueRet("")
}

func (e *Env) StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(fn ast.Obj, fnTemplateFcFn *ast.FnObj, fnTStruct *ast.FnTStruct) glob.GlobRet {
	if fnTemplateFcFn != nil {
		fnTStruct, ret := e.GetFnStructFromFnTName(fnTemplateFcFn)
		if ret.IsErr() {
			return ret
		}

		ret = e.InsertFnInFnTT(fn, fnTStruct)
		if ret.IsErr() {
			return ret
		}

		return glob.TrueRet("")
	} else {
		ret := e.InsertFnInFnTT(fn, fnTStruct)
		if ret.IsErr() {
			return ret
		}

		return glob.TrueRet("")
	}
}

func (e *Env) getInstantiatedFnTTOfFcFn(fcFn *ast.FnObj) (*ast.FnTStruct, bool, glob.GlobRet) {
	if ast.IsFnTemplate_ObjFn(fcFn) {
		fnTNoName, err := fcFn.FnTObj_ToFnTNoName()
		if err != nil {
			return nil, false, glob.ErrRet(err)
		}
		return fnTNoName, true, glob.TrueRet("")
	}

	def := e.GetFnTemplateDef(fcFn.FnHead.(ast.Atom))
	if def == nil {
		return nil, false, glob.TrueRet("")
	}

	fnTNoName, err := def.Instantiate_GetFnTemplateNoName(fcFn)
	if err != nil {
		return nil, false, glob.ErrRet(err)
	}

	return fnTNoName, true, glob.TrueRet("")
}
