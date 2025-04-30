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

package litex_memory

import (
	"fmt"
	ast "golitex/litex_ast"
)

func NewSpecFactMemDict() *SpecFactMemDict {
	return &SpecFactMemDict{map[string]map[string]StoredSpecMemDictNode{}}
}

func (factMem *SpecFactMemDict) GetNode(stmt *ast.SpecFactStmt) (StoredSpecMemDictNodeNode, bool) {
	pkgMap, pkgExists := factMem.Dict[stmt.PropName.PkgName] // 检查 pkgName 是否存在
	if !pkgExists {
		return StoredSpecMemDictNodeNode{}, false // 返回零值
	}
	node, nodeExists := pkgMap[stmt.PropName.Name] // 检查 value 是否存在
	if !nodeExists {
		return StoredSpecMemDictNodeNode{}, false // 返回零值
	}

	switch stmt.TypeEnum {
	case ast.TrueAtom:
		return node.PureFacts, true
	case ast.FalseAtom:
		return node.NotPureFacts, true
	case ast.TrueExist:
		return node.ExistFacts, true
	case ast.FalseExist:
		return node.NotExistFacts, true
	case ast.TrueExist_St:
		return node.Exist_St_Facts, true
	case ast.FalseExist_St:
		return node.NotExist_St_Facts, true
	default:
		panic("unknown spec fact type")
	}
}

func NewCondFactMemDict() *CondFactMemDict {
	return &CondFactMemDict{map[string]map[string]StoredCondFuncMemDictNode{}}
}

func (factMem *CondFactMemDict) Insert(condStmt *ast.CondFactStmt) error {
	for _, stmt := range condStmt.ThenFacts {
		if stmtAsSpecFact, ok := stmt.(*ast.SpecFactStmt); ok {
			err := factMem.InsertSpecFact(condStmt, stmtAsSpecFact)
			if err != nil {
				return err
			}
		} else if stmtAsCondFact, ok := stmt.(*ast.LogicExprStmt); ok {
			err := factMem.InsertCondFactUnderLogicExpr(condStmt, stmtAsCondFact)
			if err != nil {
				return err
			}
		} else {
			return fmt.Errorf("TODO: Currently only support spec fact in cond fact, but got: %s", stmt.String())
		}
	}
	return nil
}

func (factMem *CondFactMemDict) InsertSpecFact(condStmt *ast.CondFactStmt, stmt *ast.SpecFactStmt) error {
	// 检查 pkgName 是否存在，不存在则初始化
	pkgName := stmt.PropName.PkgName
	optName := stmt.PropName.Name

	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
		factMem.SpecFactsDict[pkgName] = make(map[string]StoredCondFuncMemDictNode)
	}

	// 获取或初始化节点
	node, nodeExists := factMem.SpecFactsDict[pkgName][optName]
	if !nodeExists {
		node = *NewStoredCondFuncMemDictNode()
	}

	switch stmt.TypeEnum {
	case ast.TrueAtom:
		node.PureFacts.Facts = append(node.PureFacts.Facts, StoredCondSpecFact{stmt, condStmt})
	case ast.FalseAtom:
		node.NotPureFacts.Facts = append(node.NotPureFacts.Facts, StoredCondSpecFact{stmt, condStmt})
	case ast.TrueExist:
		node.ExistFacts.Facts = append(node.ExistFacts.Facts, StoredCondSpecFact{stmt, condStmt})
	case ast.FalseExist:
		node.NotExistFacts.Facts = append(node.NotExistFacts.Facts, StoredCondSpecFact{stmt, condStmt})
	case ast.TrueExist_St:
		node.Exist_St_Facts.Facts = append(node.Exist_St_Facts.Facts, StoredCondSpecFact{stmt, condStmt})
	case ast.FalseExist_St:
		node.NotExist_St_Facts.Facts = append(node.NotExist_St_Facts.Facts, StoredCondSpecFact{stmt, condStmt})
	default:
		panic("unknown spec fact type")
	}

	// 更新回字典
	factMem.SpecFactsDict[pkgName][optName] = node
	return nil
}

func (factMem *CondFactMemDict) InsertCondFactUnderLogicExpr(condStmt *ast.CondFactStmt, logicExpr *ast.LogicExprStmt) error {
	pairs, err := logicExpr.SpecFactIndexPairs([]uint8{})
	if err != nil {
		return err
	}

	for _, pair := range pairs {
		stmt := pair.Stmt
		indexes := pair.Indexes

		pkgMap, pkgExists := factMem.SpecFactsDict[stmt.PropName.PkgName]
		if !pkgExists {
			factMem.SpecFactsDict[stmt.PropName.PkgName] = make(map[string]StoredCondFuncMemDictNode)
			pkgMap = factMem.SpecFactsDict[stmt.PropName.PkgName]
		}

		node, nodeExists := pkgMap[stmt.PropName.Name]
		if !nodeExists {
			node = *NewStoredCondFuncMemDictNode()
		}

		switch stmt.TypeEnum {
		case ast.TrueAtom:
			node.PureFacts.FactsInLogicExpr = append(node.PureFacts.FactsInLogicExpr, StoredCondSpecFactUnderLogicExpr{stmt, condStmt, indexes, logicExpr})
		case ast.FalseAtom:
			node.NotPureFacts.FactsInLogicExpr = append(node.NotPureFacts.FactsInLogicExpr, StoredCondSpecFactUnderLogicExpr{stmt, condStmt, indexes, logicExpr})
		case ast.TrueExist:
			node.ExistFacts.FactsInLogicExpr = append(node.ExistFacts.FactsInLogicExpr, StoredCondSpecFactUnderLogicExpr{stmt, condStmt, indexes, logicExpr})
		case ast.FalseExist:
			node.NotExistFacts.FactsInLogicExpr = append(node.NotExistFacts.FactsInLogicExpr, StoredCondSpecFactUnderLogicExpr{stmt, condStmt, indexes, logicExpr})
		case ast.TrueExist_St:
			node.Exist_St_Facts.FactsInLogicExpr = append(node.Exist_St_Facts.FactsInLogicExpr, StoredCondSpecFactUnderLogicExpr{stmt, condStmt, indexes, logicExpr})
		case ast.FalseExist_St:
			node.NotExist_St_Facts.FactsInLogicExpr = append(node.NotExist_St_Facts.FactsInLogicExpr, StoredCondSpecFactUnderLogicExpr{stmt, condStmt, indexes, logicExpr})
		default:
			return fmt.Errorf("unknown spec fact type: %s", stmt.String())
		}

		pkgMap[stmt.PropName.Name] = node
	}

	return nil
}

func (factMem *CondFactMemDict) GetSpecFactNode(stmt *ast.SpecFactStmt) (StoredCondFuncMemDictNodeNode, bool) {
	pkgName := stmt.PropName.PkgName
	optName := stmt.PropName.Name

	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
		return StoredCondFuncMemDictNodeNode{}, false
	}

	if storedFacts, optExists := factMem.SpecFactsDict[pkgName][optName]; !optExists {
		return StoredCondFuncMemDictNodeNode{}, false
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

func (factMem *UniFactMemDict) Insert(fact *ast.ConUniFactStmt) error {
	if fact.IffFacts == nil || len(fact.IffFacts) == 0 {
		return factMem.insertFacts(fact, fact.ThenFacts)
	} else {
		thenToIff := fact.NewUniFactWithThenToIff()
		err := factMem.insertFacts(thenToIff, thenToIff.ThenFacts)
		if err != nil {
			return err
		}
		iffToThen := fact.NewUniFactWithIffToThen()
		err = factMem.insertFacts(iffToThen, iffToThen.ThenFacts)
		if err != nil {
			return err
		}
	}
	return nil
}

func (factMem *UniFactMemDict) insertSpecFact(uniStmt *ast.ConUniFactStmt, stmt *ast.SpecFactStmt) error {
	// 检查 pkgName 是否存在，不存在则初始化
	pkgName := stmt.PropName.PkgName
	optName := stmt.PropName.Name

	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
		factMem.SpecFactsDict[pkgName] = make(map[string]StoredUniFuncMemDictNode)
	}

	// 获取或初始化节点
	node, nodeExists := factMem.SpecFactsDict[pkgName][optName]
	if !nodeExists {
		node = *NewStoredUniFuncMemDictNode()
	}

	if stmt.TypeEnum == ast.TrueAtom {
		node.PureFacts.Facts = append(node.PureFacts.Facts, StoredUniSpecFact{stmt, uniStmt})
	} else if stmt.TypeEnum == ast.FalseAtom {
		node.NotPureFacts.Facts = append(node.NotPureFacts.Facts, StoredUniSpecFact{stmt, uniStmt})
	} else if stmt.TypeEnum == ast.TrueExist {
		node.ExistFacts.Facts = append(node.ExistFacts.Facts, StoredUniSpecFact{stmt, uniStmt})
	} else if stmt.TypeEnum == ast.FalseExist {
		node.NotExistFacts.Facts = append(node.NotExistFacts.Facts, StoredUniSpecFact{stmt, uniStmt})
	} else if stmt.TypeEnum == ast.TrueExist_St {
		node.Exist_St_Facts.Facts = append(node.Exist_St_Facts.Facts, StoredUniSpecFact{stmt, uniStmt})
	} else if stmt.TypeEnum == ast.FalseExist_St {
		node.NotExist_St_Facts.Facts = append(node.NotExist_St_Facts.Facts, StoredUniSpecFact{stmt, uniStmt})
	} else {
		panic("unknown spec fact type")
	}

	// 更新回字典
	factMem.SpecFactsDict[pkgName][optName] = node
	return nil
}

func (factMem *UniFactMemDict) InsertCondFactUnderLogicExpr(uniStmt *ast.ConUniFactStmt, logicExpr *ast.LogicExprStmt) error {
	pairs, err := logicExpr.SpecFactIndexPairs([]uint8{})
	if err != nil {
		return err
	}

	for _, pair := range pairs {
		stmt := pair.Stmt
		indexes := pair.Indexes

		pkgMap, pkgExists := factMem.SpecFactsDict[stmt.PropName.PkgName]
		if !pkgExists {
			factMem.SpecFactsDict[stmt.PropName.PkgName] = make(map[string]StoredUniFuncMemDictNode)
			pkgMap = factMem.SpecFactsDict[stmt.PropName.PkgName]
		}

		node, nodeExists := pkgMap[stmt.PropName.Name]
		if !nodeExists {
			node = *NewStoredUniFuncMemDictNode()
		}

		switch stmt.TypeEnum {
		case ast.TrueAtom:
			node.PureFacts.FactsInLogicExpr = append(node.PureFacts.FactsInLogicExpr, StoredUniSpecFactUnderLogicExpr{stmt, uniStmt, indexes, logicExpr})
		case ast.FalseAtom:
			node.NotPureFacts.FactsInLogicExpr = append(node.NotPureFacts.FactsInLogicExpr, StoredUniSpecFactUnderLogicExpr{stmt, uniStmt, indexes, logicExpr})
		case ast.TrueExist:
			node.ExistFacts.FactsInLogicExpr = append(node.ExistFacts.FactsInLogicExpr, StoredUniSpecFactUnderLogicExpr{stmt, uniStmt, indexes, logicExpr})
		case ast.FalseExist:
			node.NotExistFacts.FactsInLogicExpr = append(node.NotExistFacts.FactsInLogicExpr, StoredUniSpecFactUnderLogicExpr{stmt, uniStmt, indexes, logicExpr})
		case ast.TrueExist_St:
			node.Exist_St_Facts.FactsInLogicExpr = append(node.Exist_St_Facts.FactsInLogicExpr, StoredUniSpecFactUnderLogicExpr{stmt, uniStmt, indexes, logicExpr})
		case ast.FalseExist_St:
			node.NotExist_St_Facts.FactsInLogicExpr = append(node.NotExist_St_Facts.FactsInLogicExpr, StoredUniSpecFactUnderLogicExpr{stmt, uniStmt, indexes, logicExpr})
		default:
			return fmt.Errorf("unknown spec fact type: %s", stmt.String())
		}

		pkgMap[stmt.PropName.Name] = node
	}

	return nil
}

func NewUniFactMemDict() *UniFactMemDict {
	return &UniFactMemDict{map[string]map[string]StoredUniFuncMemDictNode{}}
}

func (factMem *UniFactMemDict) GetSpecFactNodeWithTheSameIsTrue(stmt *ast.SpecFactStmt) (StoredUniFuncMemDictNodeNode, bool) {
	pkgName := stmt.PropName.PkgName
	optName := stmt.PropName.Name

	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
		return StoredUniFuncMemDictNodeNode{}, false
	}

	if storedFacts, optExists := factMem.SpecFactsDict[pkgName][optName]; !optExists {
		return StoredUniFuncMemDictNodeNode{}, false
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

func (storedFact *StoredSpecFact) Params() []ast.Fc {
	return storedFact.Fact.Params
}

func (storedFact *StoredSpecFact) TypeEnum() ast.SpecFactEnum {
	return storedFact.Fact.TypeEnum
}

func (factMem *SpecFactMemDict) InsertSpecFact(stmt *ast.SpecFactStmt) error {
	pkgMap, pkgExists := factMem.Dict[stmt.PropName.PkgName] // 检查 pkgName 是否存在

	// 如果包不存在，初始化包映射
	if !pkgExists {
		factMem.Dict[stmt.PropName.PkgName] = make(map[string]StoredSpecMemDictNode)
		pkgMap = factMem.Dict[stmt.PropName.PkgName]
	}

	// 获取或创建节点
	node, nodeExists := pkgMap[stmt.PropName.Name]
	if !nodeExists {
		// node = StoredSpecMemDictNode{
		// 	Facts: []StoredSpecFact{},
		// }
		// TODO: Implement this
		node = *NewStoredSpecMemDictNode()
	}

	switch stmt.TypeEnum {
	case ast.TrueAtom:
		node.PureFacts.Facts = append(node.PureFacts.Facts, StoredSpecFact{stmt})
	case ast.FalseAtom:
		node.NotPureFacts.Facts = append(node.NotPureFacts.Facts, StoredSpecFact{stmt})
	case ast.TrueExist:
		node.ExistFacts.Facts = append(node.ExistFacts.Facts, StoredSpecFact{stmt})
	case ast.FalseExist:
		node.NotExistFacts.Facts = append(node.NotExistFacts.Facts, StoredSpecFact{stmt})
	case ast.TrueExist_St:
		node.Exist_St_Facts.Facts = append(node.Exist_St_Facts.Facts, StoredSpecFact{stmt})
	case ast.FalseExist_St:
		node.NotExist_St_Facts.Facts = append(node.NotExist_St_Facts.Facts, StoredSpecFact{stmt})
	default:
		return fmt.Errorf("unknown spec fact type: %s", stmt.String())
	}

	// 更新映射中的节点
	pkgMap[stmt.PropName.Name] = node

	return nil
}

func (factMem *SpecFactMemDict) InsertSpecFactInLogicExpr(logicExpr *ast.LogicExprStmt) error {
	pairs, err := logicExpr.SpecFactIndexPairs([]uint8{})
	if err != nil {
		return err
	}

	for _, pair := range pairs {
		stmt := pair.Stmt
		indexes := pair.Indexes

		pkgMap, pkgExists := factMem.Dict[stmt.PropName.PkgName] // 检查 pkgName 是否存在

		// 如果包不存在，初始化包映射
		if !pkgExists {
			factMem.Dict[stmt.PropName.PkgName] = make(map[string]StoredSpecMemDictNode)
			pkgMap = factMem.Dict[stmt.PropName.PkgName]
		}

		node, nodeExists := pkgMap[stmt.PropName.Name]
		if !nodeExists {
			node = *NewStoredSpecMemDictNode()
		}

		switch stmt.TypeEnum {
		case ast.TrueAtom:
			node.PureFacts.FactsINLogicExpr = append(node.PureFacts.FactsINLogicExpr, StoredSpecFactInLogicExpr{stmt, indexes, logicExpr})
		case ast.FalseAtom:
			node.NotPureFacts.FactsINLogicExpr = append(node.NotPureFacts.FactsINLogicExpr, StoredSpecFactInLogicExpr{stmt, indexes, logicExpr})
		case ast.TrueExist:
			node.ExistFacts.FactsINLogicExpr = append(node.ExistFacts.FactsINLogicExpr, StoredSpecFactInLogicExpr{stmt, indexes, logicExpr})
		case ast.FalseExist:
			node.NotExistFacts.FactsINLogicExpr = append(node.NotExistFacts.FactsINLogicExpr, StoredSpecFactInLogicExpr{stmt, indexes, logicExpr})
		case ast.TrueExist_St:
			node.Exist_St_Facts.FactsINLogicExpr = append(node.Exist_St_Facts.FactsINLogicExpr, StoredSpecFactInLogicExpr{stmt, indexes, logicExpr})
		case ast.FalseExist_St:
			node.NotExist_St_Facts.FactsINLogicExpr = append(node.NotExist_St_Facts.FactsINLogicExpr, StoredSpecFactInLogicExpr{stmt, indexes, logicExpr})
		default:
			return fmt.Errorf("unknown spec fact type: %s", stmt.String())
		}

		pkgMap[stmt.PropName.Name] = node
	}

	return nil
}

func (fact *StoredSpecFactInLogicExpr) String() string {
	return fact.LogicExpr.String()
}

func NewStoredSpecMemDictNode() *StoredSpecMemDictNode {
	return &StoredSpecMemDictNode{
		PureFacts: StoredSpecMemDictNodeNode{
			Facts:            []StoredSpecFact{},
			FactsINLogicExpr: []StoredSpecFactInLogicExpr{},
		},
		NotPureFacts: StoredSpecMemDictNodeNode{
			Facts:            []StoredSpecFact{},
			FactsINLogicExpr: []StoredSpecFactInLogicExpr{},
		},
		ExistFacts: StoredSpecMemDictNodeNode{
			Facts:            []StoredSpecFact{},
			FactsINLogicExpr: []StoredSpecFactInLogicExpr{},
		},
		NotExistFacts: StoredSpecMemDictNodeNode{
			Facts:            []StoredSpecFact{},
			FactsINLogicExpr: []StoredSpecFactInLogicExpr{},
		},
		Exist_St_Facts: StoredSpecMemDictNodeNode{
			Facts:            []StoredSpecFact{},
			FactsINLogicExpr: []StoredSpecFactInLogicExpr{},
		},
		NotExist_St_Facts: StoredSpecMemDictNodeNode{
			Facts:            []StoredSpecFact{},
			FactsINLogicExpr: []StoredSpecFactInLogicExpr{},
		},
	}
}

func NewStoredCondFuncMemDictNode() *StoredCondFuncMemDictNode {
	return &StoredCondFuncMemDictNode{
		PureFacts: StoredCondFuncMemDictNodeNode{
			Facts:            []StoredCondSpecFact{},
			FactsInLogicExpr: []StoredCondSpecFactUnderLogicExpr{},
		},
		NotPureFacts: StoredCondFuncMemDictNodeNode{
			Facts:            []StoredCondSpecFact{},
			FactsInLogicExpr: []StoredCondSpecFactUnderLogicExpr{},
		},
		ExistFacts: StoredCondFuncMemDictNodeNode{
			Facts:            []StoredCondSpecFact{},
			FactsInLogicExpr: []StoredCondSpecFactUnderLogicExpr{},
		},
		NotExistFacts: StoredCondFuncMemDictNodeNode{
			Facts:            []StoredCondSpecFact{},
			FactsInLogicExpr: []StoredCondSpecFactUnderLogicExpr{},
		},
		Exist_St_Facts: StoredCondFuncMemDictNodeNode{
			Facts:            []StoredCondSpecFact{},
			FactsInLogicExpr: []StoredCondSpecFactUnderLogicExpr{},
		},
		NotExist_St_Facts: StoredCondFuncMemDictNodeNode{
			Facts:            []StoredCondSpecFact{},
			FactsInLogicExpr: []StoredCondSpecFactUnderLogicExpr{},
		},
	}
}

func NewStoredUniFuncMemDictNode() *StoredUniFuncMemDictNode {
	return &StoredUniFuncMemDictNode{
		PureFacts: StoredUniFuncMemDictNodeNode{
			Facts:            []StoredUniSpecFact{},
			FactsInLogicExpr: []StoredUniSpecFactUnderLogicExpr{},
		},
		NotPureFacts: StoredUniFuncMemDictNodeNode{
			Facts:            []StoredUniSpecFact{},
			FactsInLogicExpr: []StoredUniSpecFactUnderLogicExpr{},
		},
		ExistFacts: StoredUniFuncMemDictNodeNode{
			Facts:            []StoredUniSpecFact{},
			FactsInLogicExpr: []StoredUniSpecFactUnderLogicExpr{},
		},
		NotExistFacts: StoredUniFuncMemDictNodeNode{
			Facts:            []StoredUniSpecFact{},
			FactsInLogicExpr: []StoredUniSpecFactUnderLogicExpr{},
		},
		Exist_St_Facts: StoredUniFuncMemDictNodeNode{
			Facts:            []StoredUniSpecFact{},
			FactsInLogicExpr: []StoredUniSpecFactUnderLogicExpr{},
		},
		NotExist_St_Facts: StoredUniFuncMemDictNodeNode{
			Facts:            []StoredUniSpecFact{},
			FactsInLogicExpr: []StoredUniSpecFactUnderLogicExpr{},
		},
	}
}

func (factMem *UniFactMemDict) mergeOuterInnerUniFactAndInsert(outer *ast.ConUniFactStmt, inner *ast.ConUniFactStmt) error {
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

func (factMem *UniFactMemDict) insertFacts(uniStmt *ast.ConUniFactStmt, thenFacts []ast.FactStmt) error {
	for _, stmt := range thenFacts {
		if stmtAsSpecFact, ok := stmt.(*ast.SpecFactStmt); ok {
			err := factMem.insertSpecFact(uniStmt, stmtAsSpecFact)
			if err != nil {
				return err
			}
		} else if stmtAsConUniFact, ok := stmt.(*ast.ConUniFactStmt); ok {
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
