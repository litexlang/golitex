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
	"fmt"
	ast "golitex/litex_ast"
)

func (factMem *UniFactMem) Insert(fact *ast.UniFactStmt) error {
	if fact.IffFacts == nil || len(fact.IffFacts) == 0 {
		return factMem.insertFacts(fact)
	} else {
		thenToIff := fact.NewUniFactWithThenToIff()
		err := factMem.insertFacts(thenToIff)
		if err != nil {
			return err
		}
		iffToThen := fact.NewUniFactWithIffToThen()
		err = factMem.insertFacts(iffToThen)
		if err != nil {
			return err
		}
	}
	return nil
}

func (factMem *UniFactMem) insertSpecFact(uniStmt *ast.UniFactStmt, stmt *ast.SpecFactStmt) error {
	// 检查 pkgName 是否存在，不存在则初始化
	pkgName := stmt.PropName.PkgName
	optName := stmt.PropName.Name

	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
		factMem.SpecFactsDict[pkgName] = make(map[string]UniFactMemItem)
	}

	// 获取或初始化节点
	node, nodeExists := factMem.SpecFactsDict[pkgName][optName]
	if !nodeExists {
		node = *NewStoredUniFuncMemDictNode()
	}

	if stmt.TypeEnum == ast.TrueAtom {
		node.PureFacts.Facts = append(node.PureFacts.Facts, KnownSpecFact_InUniSpecFact{stmt, uniStmt})
	} else if stmt.TypeEnum == ast.FalseAtom {
		node.NotPureFacts.Facts = append(node.NotPureFacts.Facts, KnownSpecFact_InUniSpecFact{stmt, uniStmt})
	} else if stmt.TypeEnum == ast.TrueExist {
		node.ExistFacts.Facts = append(node.ExistFacts.Facts, KnownSpecFact_InUniSpecFact{stmt, uniStmt})
	} else if stmt.TypeEnum == ast.FalseExist {
		node.NotExistFacts.Facts = append(node.NotExistFacts.Facts, KnownSpecFact_InUniSpecFact{stmt, uniStmt})
	} else if stmt.TypeEnum == ast.TrueExist_St {
		node.Exist_St_Facts.Facts = append(node.Exist_St_Facts.Facts, KnownSpecFact_InUniSpecFact{stmt, uniStmt})
	} else if stmt.TypeEnum == ast.FalseExist_St {
		node.NotExist_St_Facts.Facts = append(node.NotExist_St_Facts.Facts, KnownSpecFact_InUniSpecFact{stmt, uniStmt})
	} else {
		panic("unknown spec fact type")
	}

	// 更新回字典
	factMem.SpecFactsDict[pkgName][optName] = node
	return nil
}

func (factMem *UniFactMem) InsertCondFactUnderLogicExpr(uniStmt *ast.UniFactStmt, logicExpr *ast.LogicExprStmt) error {
	pairs, err := logicExpr.SpecFactIndexPairs([]uint8{})
	if err != nil {
		return err
	}

	for _, pair := range pairs {
		stmt := pair.Stmt
		indexes := pair.Indexes

		pkgMap, pkgExists := factMem.SpecFactsDict[stmt.PropName.PkgName]
		if !pkgExists {
			factMem.SpecFactsDict[stmt.PropName.PkgName] = make(map[string]UniFactMemItem)
			pkgMap = factMem.SpecFactsDict[stmt.PropName.PkgName]
		}

		node, nodeExists := pkgMap[stmt.PropName.Name]
		if !nodeExists {
			node = *NewStoredUniFuncMemDictNode()
		}

		switch stmt.TypeEnum {
		case ast.TrueAtom:
			node.PureFacts.ParentLogicFacts = append(node.PureFacts.ParentLogicFacts, KnownSpecFact_InLogicExpr_InUniFact{stmt, uniStmt, indexes, logicExpr})
		case ast.FalseAtom:
			node.NotPureFacts.ParentLogicFacts = append(node.NotPureFacts.ParentLogicFacts, KnownSpecFact_InLogicExpr_InUniFact{stmt, uniStmt, indexes, logicExpr})
		case ast.TrueExist:
			node.ExistFacts.ParentLogicFacts = append(node.ExistFacts.ParentLogicFacts, KnownSpecFact_InLogicExpr_InUniFact{stmt, uniStmt, indexes, logicExpr})
		case ast.FalseExist:
			node.NotExistFacts.ParentLogicFacts = append(node.NotExistFacts.ParentLogicFacts, KnownSpecFact_InLogicExpr_InUniFact{stmt, uniStmt, indexes, logicExpr})
		case ast.TrueExist_St:
			node.Exist_St_Facts.ParentLogicFacts = append(node.Exist_St_Facts.ParentLogicFacts, KnownSpecFact_InLogicExpr_InUniFact{stmt, uniStmt, indexes, logicExpr})
		case ast.FalseExist_St:
			node.NotExist_St_Facts.ParentLogicFacts = append(node.NotExist_St_Facts.ParentLogicFacts, KnownSpecFact_InLogicExpr_InUniFact{stmt, uniStmt, indexes, logicExpr})
		default:
			return fmt.Errorf("unknown spec fact type: %s", stmt.String())
		}

		pkgMap[stmt.PropName.Name] = node
	}

	return nil
}

func NewUniFactMemDict() *UniFactMem {
	return &UniFactMem{map[string]map[string]UniFactMemItem{}}
}

func (factMem *UniFactMem) GetSpecFactNodeWithTheSameIsTrue(stmt *ast.SpecFactStmt) (EnumUniFactMem, bool) {
	pkgName := stmt.PropName.PkgName
	optName := stmt.PropName.Name

	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
		return EnumUniFactMem{}, false
	}

	if storedFacts, optExists := factMem.SpecFactsDict[pkgName][optName]; !optExists {
		return EnumUniFactMem{}, false
	} else {
		if stmt.TypeEnum == ast.TrueAtom {
			return storedFacts.PureFacts, true
		} else if stmt.TypeEnum == ast.FalseAtom {
			return storedFacts.NotPureFacts, true
		} else if stmt.TypeEnum == ast.TrueExist {
			return storedFacts.ExistFacts, true
		} else if stmt.TypeEnum == ast.FalseExist {
			return storedFacts.NotExistFacts, true
		} else if stmt.TypeEnum == ast.TrueExist_St {
			return storedFacts.Exist_St_Facts, true
		} else if stmt.TypeEnum == ast.FalseExist_St {
			return storedFacts.NotExist_St_Facts, true
		} else {
			panic("unknown spec fact type")
		}
	}
}

func (storedFact *KnownSpecFact) Params() []ast.Fc {
	return storedFact.Fact.Params
}

func (storedFact *KnownSpecFact) TypeEnum() ast.SpecFactEnum {
	return storedFact.Fact.TypeEnum
}

func (fact *KnownSpecFact_InLogicExpr) String() string {
	return fact.LogicExpr.String()
}

func NewStoredUniFuncMemDictNode() *UniFactMemItem {
	return &UniFactMemItem{
		PureFacts: EnumUniFactMem{
			Facts:            []KnownSpecFact_InUniSpecFact{},
			ParentLogicFacts: []KnownSpecFact_InLogicExpr_InUniFact{},
		},
		NotPureFacts: EnumUniFactMem{
			Facts:            []KnownSpecFact_InUniSpecFact{},
			ParentLogicFacts: []KnownSpecFact_InLogicExpr_InUniFact{},
		},
		ExistFacts: EnumUniFactMem{
			Facts:            []KnownSpecFact_InUniSpecFact{},
			ParentLogicFacts: []KnownSpecFact_InLogicExpr_InUniFact{},
		},
		NotExistFacts: EnumUniFactMem{
			Facts:            []KnownSpecFact_InUniSpecFact{},
			ParentLogicFacts: []KnownSpecFact_InLogicExpr_InUniFact{},
		},
		Exist_St_Facts: EnumUniFactMem{
			Facts:            []KnownSpecFact_InUniSpecFact{},
			ParentLogicFacts: []KnownSpecFact_InLogicExpr_InUniFact{},
		},
		NotExist_St_Facts: EnumUniFactMem{
			Facts:            []KnownSpecFact_InUniSpecFact{},
			ParentLogicFacts: []KnownSpecFact_InLogicExpr_InUniFact{},
		},
	}
}

func (factMem *UniFactMem) mergeOuterInnerUniFactAndInsert(outer *ast.UniFactStmt, inner *ast.UniFactStmt) error {
	mergedConUni := ast.MergeOuterInnerUniFacts(outer, inner)
	thenFacts := []*ast.SpecFactStmt{}
	for _, stmt := range mergedConUni.ThenFacts {
		if stmtAsSpecFact, ok := stmt.(*ast.SpecFactStmt); ok {
			thenFacts = append(thenFacts, stmtAsSpecFact)
		} else {
			return fmt.Errorf("TODO: Currently only support spec fact in uni fact, but got: %s", stmt.String())
		}
	}

	for _, specFact := range thenFacts {
		err := factMem.insertSpecFact(mergedConUni, specFact)
		if err != nil {
			return err
		}
	}

	return nil
}

func (factMem *UniFactMem) insertFacts(uniStmt *ast.UniFactStmt) error {
	for _, stmt := range uniStmt.ThenFacts {
		if stmtAsSpecFact, ok := stmt.(*ast.SpecFactStmt); ok {
			if stmtAsSpecFact.IsSpecFactNameWithUniPrefix() {
				return fmt.Errorf("facts in the body of universal fact should not be a free fact, got %s", stmtAsSpecFact.String())
			}

			err := factMem.insertSpecFact(uniStmt, stmtAsSpecFact)
			if err != nil {
				return err
			}
		} else if stmtAsConUniFact, ok := stmt.(*ast.UniFactStmt); ok {
			err := factMem.mergeOuterInnerUniFactAndInsert(uniStmt, stmtAsConUniFact)
			if err != nil {
				return err
			}
		} else {
			return fmt.Errorf("TODO: Currently only support spec fact in uni fact, but got: %s", stmt.String())
		}
	}
	return nil
}
