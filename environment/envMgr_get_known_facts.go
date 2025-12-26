// Copyright Jiachen Shen.
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
	ast "golitex/ast"
	glob "golitex/glob"
)

func (s SpecFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]ast.SpecFactStmt, *glob.GlobRet) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, glob.NewEmptyGlobTrue()
	case ast.FalsePure:
		return s.NotPureFacts, glob.NewEmptyGlobTrue()
	case ast.TrueExist_St:
		return s.Exist_St_Facts, glob.NewEmptyGlobTrue()
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, glob.NewEmptyGlobTrue()
	default:
		return nil, glob.ErrRet(("invalid spec fact type"))
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

func (s SpecFactMem) newFact(stmt *ast.SpecFactStmt) *glob.GlobRet {
	// 要考虑pkgName和propName是否存在
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return ret
	}

	if _, ok := sameEnumFacts[string(stmt.PropName)]; !ok {
		sameEnumFacts[string(stmt.PropName)] = []ast.SpecFactStmt{}
	}
	sameEnumFacts[string(stmt.PropName)] = append(sameEnumFacts[string(stmt.PropName)], *stmt)
	return glob.NewEmptyGlobTrue()
}

func (s SpecFactInLogicExprMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]KnownSpecFact_InLogicExpr, *glob.GlobRet) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, glob.NewEmptyGlobTrue()
	case ast.FalsePure:
		return s.NotPureFacts, glob.NewEmptyGlobTrue()
	case ast.TrueExist_St:
		return s.Exist_St_Facts, glob.NewEmptyGlobTrue()
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, glob.NewEmptyGlobTrue()
	default:
		return nil, glob.ErrRet(("invalid spec fact type"))
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

func (s SpecFactInLogicExprMem) newFact(logicExpr *ast.OrStmt) *glob.GlobRet {
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

	return glob.NewEmptyGlobTrue()
}

func (s SpecFactInUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]KnownSpecFact_InUniFact, *glob.GlobRet) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, glob.NewEmptyGlobTrue()
	case ast.FalsePure:
		return s.NotPureFacts, glob.NewEmptyGlobTrue()
	case ast.TrueExist_St:
		return s.Exist_St_Facts, glob.NewEmptyGlobTrue()
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, glob.NewEmptyGlobTrue()
	default:
		return nil, glob.ErrRet(("invalid spec fact type"))
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

func (s SpecFactInUniFactMem) newFact(stmtAsSpecFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt) *glob.GlobRet {
	sameEnumFacts, ret := s.getSameEnumFacts(stmtAsSpecFact)
	if ret.IsErr() {
		return ret
	}

	if _, ok := sameEnumFacts[string(stmtAsSpecFact.PropName)]; !ok {
		sameEnumFacts[string(stmtAsSpecFact.PropName)] = []KnownSpecFact_InUniFact{}
	}
	sameEnumFacts[string(stmtAsSpecFact.PropName)] = append(sameEnumFacts[string(stmtAsSpecFact.PropName)], KnownSpecFact_InUniFact{stmtAsSpecFact, uniFact})

	return glob.NewEmptyGlobTrue()
}

func (s SpecFact_InLogicExpr_InUniFactMem) getSameEnumFacts(stmt *ast.SpecFactStmt) (map[string][]SpecFact_InLogicExpr_InUniFact, *glob.GlobRet) {
	switch stmt.TypeEnum {
	case ast.TruePure:
		return s.PureFacts, glob.NewEmptyGlobTrue()
	case ast.FalsePure:
		return s.NotPureFacts, glob.NewEmptyGlobTrue()
	case ast.TrueExist_St:
		return s.Exist_St_Facts, glob.NewEmptyGlobTrue()
	case ast.FalseExist_St:
		return s.NotExist_St_Facts, glob.NewEmptyGlobTrue()
	default:
		return nil, glob.ErrRet(("invalid spec fact type"))
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

func (s SpecFact_InLogicExpr_InUniFactMem) NewFact(uniStmt *ast.UniFactStmt, logicExpr *ast.OrStmt) *glob.GlobRet {
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

	return glob.NewEmptyGlobTrue()
}

func (envMemory *EnvMemory) GetEqualObjs(obj ast.Obj) (*[]ast.Obj, bool) {
	objAsStr := obj.String()
	facts, ok := envMemory.EqualMem[objAsStr]
	return facts, ok
}
