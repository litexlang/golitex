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
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

// func getSameEnumFacts[T ast.SpecificFactStmt](s *SpecFactMem, stmt ast.SpecificFactStmt) (map[string][]T, *glob.StmtRet) {
// 	switch asFact := stmt.(type) {
// 	case *ast.PureSpecificFactStmt:
// 		if asFact.IsTrue {
// 			return s.PureFacts, glob.NewEmptyStmtTrue()
// 		} else {
// 			return s.NotPureFacts.(SpecificFactStmtMap), glob.NewEmptyStmtTrue()
// 		}
// 	case *ast.ExistSpecificFactStmt:
// 		if asFact.IsTrue {
// 			return s.Exist_St_Facts.(SpecificFactStmtMap), glob.NewEmptyStmtTrue()
// 		} else {
// 			return s.NotExist_St_Facts.(SpecificFactStmtMap), glob.NewEmptyStmtTrue()
// 		}
// 	default:
// 		return nil, glob.ErrRet(("invalid spec fact type"))
// 	}

// 	switch stmt.FactType {
// 	case ast.TruePure:
// 		return s.PureFacts, glob.NewEmptyStmtTrue()
// 	case ast.FalsePure:
// 		return s.NotPureFacts, glob.NewEmptyStmtTrue()
// 	case ast.TrueExist_St:
// 		return s.Exist_St_Facts, glob.NewEmptyStmtTrue()
// 	case ast.FalseExist_St:
// 		return s.NotExist_St_Facts, glob.NewEmptyStmtTrue()
// 	default:
// 		return nil, glob.ErrRet(("invalid spec fact type"))
// 	}
// }

// func (s SpecFactMem) GetSameEnumPkgPropFacts(stmt ast.SpecificFactStmt) ([]ast.SpecificFactStmt, bool) {
// 	switch asFact := stmt.(type) {
// 	case *ast.PureSpecificFactStmt:
// 		if asFact.IsTrue {
// 			sameEnumPkgPropFacts, memExist := s.PureFacts[string(asFact.PropName)]
// 			if !memExist {
// 				return nil, false
// 			}
// 			return sameEnumPkgPropFacts, glob.NewEmptyStmtTrue()
// 		}
// 	}

// 	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
// 	if ret.IsErr() {
// 		return nil, false
// 	}

// 	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.GetPropName())]
// 	if !memExist {
// 		return nil, false
// 	}

// 	return sameEnumPkgPropFacts, true
// }

// func (s SpecFactMem) newFact(stmt ast.PureSpecificFactStmt) *glob.StmtRet {
// 	// 要考虑pkgName和propName是否存在
// 	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
// 	if ret.IsErr() {
// 		return ret
// 	}

// 	if _, ok := sameEnumFacts[string(stmt.PropName)]; !ok {
// 		sameEnumFacts[string(stmt.PropName)] = []ast.SpecFactStmt{}
// 	}
// 	sameEnumFacts[string(stmt.PropName)] = append(sameEnumFacts[string(stmt.PropName)], *stmt)
// 	return glob.NewEmptyStmtTrue()
// }

func (s SpecFactInLogicExprMem) getSameEnumFacts(stmt ast.SpecificFactStmt) (map[string][]KnownSpecFact_InLogicExpr, *glob.StmtRet) {
	switch asFact := stmt.(type) {
	case *ast.PureSpecificFactStmt:
		if asFact.IsTrue {
			return s.PureFacts, glob.NewEmptyStmtTrue()
		} else {
			return s.NotPureFacts, glob.NewEmptyStmtTrue()
		}
	case *ast.ExistSpecificFactStmt:
		if asFact.IsTrue {
			return s.Exist_St_Facts, glob.NewEmptyStmtTrue()
		} else {
			return s.NotExist_St_Facts, glob.NewEmptyStmtTrue()
		}
	default:
		return nil, glob.ErrRet(("invalid spec fact type"))
	}
}

func (s SpecFactInLogicExprMem) GetSameEnumPkgPropFacts(stmt ast.SpecificFactStmt) ([]KnownSpecFact_InLogicExpr, bool) {
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return nil, false
	}

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.GetPropName())]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFactInLogicExprMem) newFact(logicExpr *ast.OrStmt) *glob.StmtRet {
	for i, fact := range logicExpr.Facts {
		sameEnumFacts, ret := s.getSameEnumFacts(fact)
		if ret.IsErr() {
			return ret
		}

		if _, ok := sameEnumFacts[string(fact.GetPropName())]; !ok {
			sameEnumFacts[string(fact.GetPropName())] = []KnownSpecFact_InLogicExpr{}
		}
		sameEnumFacts[string(fact.GetPropName())] = append(sameEnumFacts[string(fact.GetPropName())], *NewKnownSpecFact_InLogicExpr(fact, i, logicExpr))
	}

	return glob.NewEmptyStmtTrue()
}

func (s SpecFactInUniFactMem) getSameEnumFacts(stmt ast.SpecificFactStmt) (map[string][]KnownSpecFact_InUniFact, *glob.StmtRet) {
	switch asFact := stmt.(type) {
	case *ast.PureSpecificFactStmt:
		if asFact.IsTrue {
			return s.PureFacts, glob.NewEmptyStmtTrue()
		} else {
			return s.NotPureFacts, glob.NewEmptyStmtTrue()
		}
	case *ast.ExistSpecificFactStmt:
		if asFact.IsTrue {
			return s.Exist_St_Facts, glob.NewEmptyStmtTrue()
		} else {
			return s.NotExist_St_Facts, glob.NewEmptyStmtTrue()
		}
	}

	return nil, glob.ErrRet(("invalid spec fact type"))
}

func (s SpecFactInUniFactMem) GetSameEnumPkgPropFacts(stmt ast.SpecificFactStmt) ([]KnownSpecFact_InUniFact, bool) {
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return nil, false
	}

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.GetPropName())]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFactInUniFactMem) newFact(stmtAsSpecFact ast.SpecificFactStmt, uniFact *ast.UniFactStmt) *glob.StmtRet {
	sameEnumFacts, ret := s.getSameEnumFacts(stmtAsSpecFact)
	if ret.IsErr() {
		return ret
	}

	if _, ok := sameEnumFacts[string(stmtAsSpecFact.GetPropName())]; !ok {
		sameEnumFacts[string(stmtAsSpecFact.GetPropName())] = []KnownSpecFact_InUniFact{}
	}
	sameEnumFacts[string(stmtAsSpecFact.GetPropName())] = append(sameEnumFacts[string(stmtAsSpecFact.GetPropName())], KnownSpecFact_InUniFact{stmtAsSpecFact, uniFact})

	return glob.NewEmptyStmtTrue()
}

func (s SpecFact_InLogicExpr_InUniFactMem) getSameEnumFacts(stmt ast.SpecificFactStmt) (map[string][]SpecFact_InLogicExpr_InUniFact, *glob.StmtRet) {
	switch asFact := stmt.(type) {
	case *ast.PureSpecificFactStmt:
		if asFact.IsTrue {
			return s.PureFacts, glob.NewEmptyStmtTrue()
		} else {
			return s.NotPureFacts, glob.NewEmptyStmtTrue()
		}
	case *ast.ExistSpecificFactStmt:
		if asFact.IsTrue {
			return s.Exist_St_Facts, glob.NewEmptyStmtTrue()
		} else {
			return s.NotExist_St_Facts, glob.NewEmptyStmtTrue()
		}
	default:
		return nil, glob.ErrRet(("invalid spec fact type"))
	}
}

func (s SpecFact_InLogicExpr_InUniFactMem) GetSameEnumPkgPropFacts(stmt ast.SpecificFactStmt) ([]SpecFact_InLogicExpr_InUniFact, bool) {
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return nil, false
	}

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.GetPropName())]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFact_InLogicExpr_InUniFactMem) NewFact(uniStmt *ast.UniFactStmt, logicExpr *ast.OrStmt) *glob.StmtRet {
	for i, fact := range logicExpr.Facts {
		sameEnumFacts, ret := s.getSameEnumFacts(fact)
		if ret.IsErr() {
			return ret
		}

		if _, ok := sameEnumFacts[string(fact.GetPropName())]; !ok {
			sameEnumFacts[string(fact.GetPropName())] = []SpecFact_InLogicExpr_InUniFact{}
		}
		sameEnumFacts[string(fact.GetPropName())] = append(sameEnumFacts[string(fact.GetPropName())], *NewSpecFact_InLogicExpr_InUniFact(fact, uniStmt, i, logicExpr))
	}

	return glob.NewEmptyStmtTrue()
}

func (s SpecFactInImplyTemplateMem) getSameEnumFacts(stmt ast.SpecificFactStmt) (map[string][]KnownSpecFact_InImplyTemplate, *glob.StmtRet) {
	switch asFact := stmt.(type) {
	case *ast.PureSpecificFactStmt:
		if asFact.IsTrue {
			return s.PureFacts, glob.NewEmptyStmtTrue()
		} else {
			return s.NotPureFacts, glob.NewEmptyStmtTrue()
		}
	case *ast.ExistSpecificFactStmt:
		if asFact.IsTrue {
			return s.Exist_St_Facts, glob.NewEmptyStmtTrue()
		} else {
			return s.NotExist_St_Facts, glob.NewEmptyStmtTrue()
		}
	default:
		return nil, glob.ErrRet(("invalid spec fact type"))
	}
}

func (s SpecFactInImplyTemplateMem) GetSameEnumPkgPropFacts(stmt ast.SpecificFactStmt) ([]KnownSpecFact_InImplyTemplate, bool) {
	sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	if ret.IsErr() {
		return nil, false
	}

	sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.GetPropName())]
	if !memExist {
		return nil, false
	}

	return sameEnumPkgPropFacts, true
}

func (s SpecFactInImplyTemplateMem) newFact(known ast.Spec_OrFact, implyTemplate *ast.InferTemplateStmt) *glob.StmtRet {
	stmtAsSpecFact, ok := known.(ast.SpecificFactStmt)
	if !ok {
		knownAsOr, ok := known.(*ast.OrStmt)
		if !ok {
			return glob.ErrRet(fmt.Sprintf("invalid known fact type: %T", known))
		}
		stmtAsSpecFact = knownAsOr.Facts[0]
	}

	sameEnumFacts, ret := s.getSameEnumFacts(stmtAsSpecFact)
	if ret.IsErr() {
		return ret
	}

	if _, ok := sameEnumFacts[string(stmtAsSpecFact.GetPropName())]; !ok {
		sameEnumFacts[string(stmtAsSpecFact.GetPropName())] = []KnownSpecFact_InImplyTemplate{}
	}
	sameEnumFacts[string(stmtAsSpecFact.GetPropName())] = append(sameEnumFacts[string(stmtAsSpecFact.GetPropName())], NewKnownSpecFact_InImplyTemplate(known, implyTemplate))

	return glob.NewEmptyStmtTrue()
}

func (envMemory *EnvMemory) GetEqualObjs(obj ast.Obj) (*[]ast.Obj, bool) {
	objAsStr := obj.String()
	facts, ok := envMemory.EqualMem[objAsStr]
	return facts, ok
}
