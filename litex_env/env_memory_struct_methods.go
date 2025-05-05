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

func NewSpecFactMemDict() *SpecFactMem {
	return &SpecFactMem{
		PureFacts:         map[string]map[string][]KnownSpecFact{},
		NotPureFacts:      map[string]map[string][]KnownSpecFact{},
		ExistFacts:        map[string]map[string][]KnownSpecFact{},
		NotExistFacts:     map[string]map[string][]KnownSpecFact{},
		Exist_St_Facts:    map[string]map[string][]KnownSpecFact{},
		NotExist_St_Facts: map[string]map[string][]KnownSpecFact{},
	}
}

// func (factMem *SpecFactMem) GetNode(stmt *ast.SpecFactStmt) (EnumSpecFactMem, bool) {
// 	pkgMap, pkgExists := factMem.Dict[stmt.PropName.PkgName] // 检查 pkgName 是否存在
// 	if !pkgExists {
// 		return EnumSpecFactMem{}, false // 返回零值
// 	}
// 	node, nodeExists := pkgMap[stmt.PropName.Name] // 检查 value 是否存在
// 	if !nodeExists {
// 		return EnumSpecFactMem{}, false // 返回零值
// 	}

// 	switch stmt.TypeEnum {
// 	case ast.TrueAtom:
// 		return node.PureFacts, true
// 	case ast.FalseAtom:
// 		return node.NotPureFacts, true
// 	case ast.TrueExist:
// 		return node.ExistFacts, true
// 	case ast.FalseExist:
// 		return node.NotExistFacts, true
// 	case ast.TrueExist_St:
// 		return node.Exist_St_Facts, true
// 	case ast.FalseExist_St:
// 		return node.NotExist_St_Facts, true
// 	default:
// 		panic("unknown spec fact type")
// 	}
// }

func (factMem *SpecFactMem) GetNode(stmt *ast.SpecFactStmt) ([]KnownSpecFact, bool) {
	var enumSpecFactMemMapMap map[string]map[string][]KnownSpecFact

	switch stmt.TypeEnum {
	case ast.TrueAtom:
		enumSpecFactMemMapMap = factMem.PureFacts
	case ast.FalseAtom:
		enumSpecFactMemMapMap = factMem.NotPureFacts
	case ast.TrueExist:
		enumSpecFactMemMapMap = factMem.ExistFacts
	case ast.FalseExist:
		enumSpecFactMemMapMap = factMem.NotExistFacts
	case ast.TrueExist_St:
		enumSpecFactMemMapMap = factMem.Exist_St_Facts
	case ast.FalseExist_St:
		enumSpecFactMemMapMap = factMem.NotExist_St_Facts
	default:
		return nil, false
	}

	enumSpecFactMemMap, memMapExist := enumSpecFactMemMapMap[stmt.PropName.PkgName] // 检查 pkgName 是否存在
	if !memMapExist {
		return nil, false // 返回零值
	}

	enumSpecFactMem, memExist := enumSpecFactMemMap[stmt.PropName.Name] // 检查 value 是否存在
	if !memExist {
		return nil, false // 返回零值
	}

	return enumSpecFactMem, true
}

// func NewCondFactMemDict() *CondFactMemDict {
// 	return &CondFactMemDict{map[string]map[string]StoredCondFuncMemDictNode{}}
// }

// func (factMem *CondFactMemDict) Insert(condStmt *ast.CondFactStmt) error {
// 	for _, stmt := range condStmt.ThenFacts {
// 		if stmtAsSpecFact, ok := stmt.(*ast.SpecFactStmt); ok {
// 			err := factMem.InsertSpecFact(condStmt, stmtAsSpecFact)
// 			if err != nil {
// 				return err
// 			}
// 		} else if stmtAsCondFact, ok := stmt.(*ast.LogicExprStmt); ok {
// 			err := factMem.InsertCondFactUnderLogicExpr(condStmt, stmtAsCondFact)
// 			if err != nil {
// 				return err
// 			}
// 		} else {
// 			return fmt.Errorf("TODO: Currently only support spec fact in cond fact, but got: %s", stmt.String())
// 		}
// 	}
// 	return nil
// }

// func (factMem *CondFactMemDict) InsertSpecFact(condStmt *ast.CondFactStmt, stmt *ast.SpecFactStmt) error {
// 	// 检查 pkgName 是否存在，不存在则初始化
// 	pkgName := stmt.PropName.PkgName
// 	optName := stmt.PropName.Name

// 	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
// 		factMem.SpecFactsDict[pkgName] = make(map[string]StoredCondFuncMemDictNode)
// 	}

// 	// 获取或初始化节点
// 	node, nodeExists := factMem.SpecFactsDict[pkgName][optName]
// 	if !nodeExists {
// 		node = *NewStoredCondFuncMemDictNode()
// 	}

// 	switch stmt.TypeEnum {
// 	case ast.TrueAtom:
// 		node.PureFacts.Facts = append(node.PureFacts.Facts, StoredCondSpecFact{stmt, condStmt})
// 	case ast.FalseAtom:
// 		node.NotPureFacts.Facts = append(node.NotPureFacts.Facts, StoredCondSpecFact{stmt, condStmt})
// 	case ast.TrueExist:
// 		node.ExistFacts.Facts = append(node.ExistFacts.Facts, StoredCondSpecFact{stmt, condStmt})
// 	case ast.FalseExist:
// 		node.NotExistFacts.Facts = append(node.NotExistFacts.Facts, StoredCondSpecFact{stmt, condStmt})
// 	case ast.TrueExist_St:
// 		node.Exist_St_Facts.Facts = append(node.Exist_St_Facts.Facts, StoredCondSpecFact{stmt, condStmt})
// 	case ast.FalseExist_St:
// 		node.NotExist_St_Facts.Facts = append(node.NotExist_St_Facts.Facts, StoredCondSpecFact{stmt, condStmt})
// 	default:
// 		panic("unknown spec fact type")
// 	}

// 	// 更新回字典
// 	factMem.SpecFactsDict[pkgName][optName] = node
// 	return nil
// }

// func (factMem *CondFactMemDict) InsertCondFactUnderLogicExpr(condStmt *ast.CondFactStmt, logicExpr *ast.LogicExprStmt) error {
// 	pairs, err := logicExpr.SpecFactIndexPairs([]uint8{})
// 	if err != nil {
// 		return err
// 	}

// 	for _, pair := range pairs {
// 		stmt := pair.Stmt
// 		indexes := pair.Indexes

// 		pkgMap, pkgExists := factMem.SpecFactsDict[stmt.PropName.PkgName]
// 		if !pkgExists {
// 			factMem.SpecFactsDict[stmt.PropName.PkgName] = make(map[string]StoredCondFuncMemDictNode)
// 			pkgMap = factMem.SpecFactsDict[stmt.PropName.PkgName]
// 		}

// 		node, nodeExists := pkgMap[stmt.PropName.Name]
// 		if !nodeExists {
// 			node = *NewStoredCondFuncMemDictNode()
// 		}

// 		switch stmt.TypeEnum {
// 		case ast.TrueAtom:
// 			node.PureFacts.FactsInLogicExpr = append(node.PureFacts.FactsInLogicExpr, StoredCondSpecFactUnderLogicExpr{stmt, condStmt, indexes, logicExpr})
// 		case ast.FalseAtom:
// 			node.NotPureFacts.FactsInLogicExpr = append(node.NotPureFacts.FactsInLogicExpr, StoredCondSpecFactUnderLogicExpr{stmt, condStmt, indexes, logicExpr})
// 		case ast.TrueExist:
// 			node.ExistFacts.FactsInLogicExpr = append(node.ExistFacts.FactsInLogicExpr, StoredCondSpecFactUnderLogicExpr{stmt, condStmt, indexes, logicExpr})
// 		case ast.FalseExist:
// 			node.NotExistFacts.FactsInLogicExpr = append(node.NotExistFacts.FactsInLogicExpr, StoredCondSpecFactUnderLogicExpr{stmt, condStmt, indexes, logicExpr})
// 		case ast.TrueExist_St:
// 			node.Exist_St_Facts.FactsInLogicExpr = append(node.Exist_St_Facts.FactsInLogicExpr, StoredCondSpecFactUnderLogicExpr{stmt, condStmt, indexes, logicExpr})
// 		case ast.FalseExist_St:
// 			node.NotExist_St_Facts.FactsInLogicExpr = append(node.NotExist_St_Facts.FactsInLogicExpr, StoredCondSpecFactUnderLogicExpr{stmt, condStmt, indexes, logicExpr})
// 		default:
// 			return fmt.Errorf("unknown spec fact type: %s", stmt.String())
// 		}

// 		pkgMap[stmt.PropName.Name] = node
// 	}

// 	return nil
// }

// func (factMem *CondFactMemDict) GetSpecFactNode(stmt *ast.SpecFactStmt) (StoredCondFuncMemDictNodeNode, bool) {
// 	pkgName := stmt.PropName.PkgName
// 	optName := stmt.PropName.Name

// 	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
// 		return StoredCondFuncMemDictNodeNode{}, false
// 	}

// 	if storedFacts, optExists := factMem.SpecFactsDict[pkgName][optName]; !optExists {
// 		return StoredCondFuncMemDictNodeNode{}, false
// 	} else {
// 		if stmt.TypeEnum == ast.TrueAtom {
// 			return storedFacts.PureFacts, true
// 		} else if stmt.TypeEnum == ast.FalseAtom {
// 			return storedFacts.NotPureFacts, true
// 		} else if stmt.TypeEnum == ast.TrueExist {
// 			return storedFacts.ExistFacts, true
// 		} else if stmt.TypeEnum == ast.FalseExist {
// 			return storedFacts.NotExistFacts, true
// 		} else if stmt.TypeEnum == ast.TrueExist_St {
// 			return storedFacts.Exist_St_Facts, true
// 		} else if stmt.TypeEnum == ast.FalseExist_St {
// 			return storedFacts.NotExist_St_Facts, true
// 		} else {
// 			panic("unknown spec fact type")
// 		}
// 	}
// }

func (factMem *UniFactMem) Insert(fact *ast.UniFactStmt) error {
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

// func (factMem *SpecFactMem) InsertSpecFact(stmt *ast.SpecFactStmt) error {
// 	pkgMap, pkgExists := factMem.Dict[stmt.PropName.PkgName] // 检查 pkgName 是否存在

// 	// 如果包不存在，初始化包映射
// 	if !pkgExists {
// 		factMem.Dict[stmt.PropName.PkgName] = make(map[string]SpecFactMemItem)
// 		pkgMap = factMem.Dict[stmt.PropName.PkgName]
// 	}

// 	// 获取或创建节点
// 	node, nodeExists := pkgMap[stmt.PropName.Name]
// 	if !nodeExists {
// 		// node = StoredSpecMemDictNode{
// 		// 	Facts: []StoredSpecFact{},
// 		// }
// 		// TODO: Implement this
// 		node = *NewStoredSpecMemDictNode()
// 	}

// 	switch stmt.TypeEnum {
// 	case ast.TrueAtom:
// 		node.PureFacts.Facts = append(node.PureFacts.Facts, KnownSpecFact{stmt})
// 	case ast.FalseAtom:
// 		node.NotPureFacts.Facts = append(node.NotPureFacts.Facts, KnownSpecFact{stmt})
// 	case ast.TrueExist:
// 		node.ExistFacts.Facts = append(node.ExistFacts.Facts, KnownSpecFact{stmt})
// 	case ast.FalseExist:
// 		node.NotExistFacts.Facts = append(node.NotExistFacts.Facts, KnownSpecFact{stmt})
// 	case ast.TrueExist_St:
// 		node.Exist_St_Facts.Facts = append(node.Exist_St_Facts.Facts, KnownSpecFact{stmt})
// 	case ast.FalseExist_St:
// 		node.NotExist_St_Facts.Facts = append(node.NotExist_St_Facts.Facts, KnownSpecFact{stmt})
// 	default:
// 		return fmt.Errorf("unknown spec fact type: %s", stmt.String())
// 	}

// 	// 更新映射中的节点
// 	pkgMap[stmt.PropName.Name] = node

// 	return nil
// }

func (factMem *SpecFactMem) makeEnumSpecFactMem(stmt *ast.SpecFactStmt) ([]KnownSpecFact, error) {
	var factsUnderPkgName map[string][]KnownSpecFact
	var factsUnderPkgNameExist bool

	switch stmt.TypeEnum {
	case ast.TrueAtom:
		factsUnderPkgName, factsUnderPkgNameExist = factMem.PureFacts[stmt.PropName.PkgName]
	case ast.FalseAtom:
		factsUnderPkgName, factsUnderPkgNameExist = factMem.NotPureFacts[stmt.PropName.PkgName]
	case ast.TrueExist:
		factsUnderPkgName, factsUnderPkgNameExist = factMem.ExistFacts[stmt.PropName.PkgName]
	case ast.FalseExist:
		factsUnderPkgName, factsUnderPkgNameExist = factMem.NotExistFacts[stmt.PropName.PkgName]
	case ast.TrueExist_St:
		factsUnderPkgName, factsUnderPkgNameExist = factMem.Exist_St_Facts[stmt.PropName.PkgName]
	case ast.FalseExist_St:
		factsUnderPkgName, factsUnderPkgNameExist = factMem.NotExist_St_Facts[stmt.PropName.PkgName]
	default:
		return nil, fmt.Errorf("unknown spec fact type: %s", stmt.String())
	}

	if !factsUnderPkgNameExist {
		switch stmt.TypeEnum {
		case ast.TrueAtom:
			factMem.PureFacts[stmt.PropName.PkgName] = make(map[string][]KnownSpecFact)
			factMem.PureFacts[stmt.PropName.PkgName][stmt.PropName.Name] = []KnownSpecFact{}
			return factMem.PureFacts[stmt.PropName.PkgName][stmt.PropName.Name], nil
		case ast.FalseAtom:
			factMem.NotPureFacts[stmt.PropName.PkgName] = make(map[string][]KnownSpecFact)
			factMem.NotPureFacts[stmt.PropName.PkgName][stmt.PropName.Name] = []KnownSpecFact{}
			return factMem.NotPureFacts[stmt.PropName.PkgName][stmt.PropName.Name], nil
		case ast.TrueExist:
			factMem.ExistFacts[stmt.PropName.PkgName] = make(map[string][]KnownSpecFact)
			factMem.ExistFacts[stmt.PropName.PkgName][stmt.PropName.Name] = []KnownSpecFact{}
			return factMem.ExistFacts[stmt.PropName.PkgName][stmt.PropName.Name], nil
		case ast.FalseExist:
			factMem.NotExistFacts[stmt.PropName.PkgName] = make(map[string][]KnownSpecFact)
			factMem.NotExistFacts[stmt.PropName.PkgName][stmt.PropName.Name] = []KnownSpecFact{}
			return factMem.NotExistFacts[stmt.PropName.PkgName][stmt.PropName.Name], nil
		case ast.TrueExist_St:
			factMem.Exist_St_Facts[stmt.PropName.PkgName] = make(map[string][]KnownSpecFact)
			factMem.Exist_St_Facts[stmt.PropName.PkgName][stmt.PropName.Name] = []KnownSpecFact{}
			return factMem.Exist_St_Facts[stmt.PropName.PkgName][stmt.PropName.Name], nil
		case ast.FalseExist_St:
			factMem.NotExist_St_Facts[stmt.PropName.PkgName] = make(map[string][]KnownSpecFact)
			factMem.NotExist_St_Facts[stmt.PropName.PkgName][stmt.PropName.Name] = []KnownSpecFact{}
			return factMem.NotExist_St_Facts[stmt.PropName.PkgName][stmt.PropName.Name], nil
		default:
			return nil, fmt.Errorf("unknown spec fact type: %s", stmt.String())
		}
	}

	factsUnderPropName, factsUnderPropNameExist := factsUnderPkgName[stmt.PropName.Name]
	if !factsUnderPropNameExist {
		switch stmt.TypeEnum {
		case ast.TrueAtom:
			factsUnderPkgName[stmt.PropName.Name] = []KnownSpecFact{}
		case ast.FalseAtom:
			factsUnderPkgName[stmt.PropName.Name] = []KnownSpecFact{}
		case ast.TrueExist:
			factsUnderPkgName[stmt.PropName.Name] = []KnownSpecFact{}
		case ast.FalseExist:
			factsUnderPkgName[stmt.PropName.Name] = []KnownSpecFact{}
		case ast.TrueExist_St:
			factsUnderPkgName[stmt.PropName.Name] = []KnownSpecFact{}
		case ast.FalseExist_St:
			factsUnderPkgName[stmt.PropName.Name] = []KnownSpecFact{}
		}
		return factsUnderPkgName[stmt.PropName.Name], nil
	}

	return factsUnderPropName, nil
}

func (factMem *SpecFactMem) newSpecFact(stmt *ast.SpecFactStmt) error {
	enumSpecFactMem, memExist := factMem.GetNode(stmt)
	if memExist {
		enumSpecFactMem = append(enumSpecFactMem, KnownSpecFact{stmt})
		return nil
	} else {
		enumSpecFactMem, err := factMem.makeEnumSpecFactMem(stmt)
		if err != nil {
			return err
		}
		enumSpecFactMem = append(enumSpecFactMem, KnownSpecFact{stmt})
		return nil
	}
}

func (factMem *SpecFactMem) InsertSpecFact(stmt *ast.SpecFactStmt) error {
	enumSpecFactMem, memExist := factMem.GetNode(stmt)
	if memExist {
		enumSpecFactMem = append(enumSpecFactMem, KnownSpecFact{stmt})
		return nil
	} else {
		enumSpecFactMem, err := factMem.makeEnumSpecFactMem(stmt)
		if err != nil {
			return err
		}
		enumSpecFactMem = append(enumSpecFactMem, KnownSpecFact{stmt})
		return nil
	}
}

func (factMem *SpecFactMem) InsertSpecFactInLogicExpr(logicExpr *ast.LogicExprStmt) error {
	return nil // TODO 等我把 interface 之类的弄好再说
	// pairs, err := logicExpr.SpecFactIndexPairs([]uint8{})
	// if err != nil {
	// 	return err
	// }

	// for _, pair := range pairs {
	// 	enumSpecFactMem, memExist := factMem.GetNode(pair.Stmt)
	// 	if memExist {
	// 		enumSpecFactMem.FactsINLogicExpr = append(enumSpecFactMem.FactsINLogicExpr, KnownSpecFact_InLogicExpr{pair.Stmt, pair.Indexes, logicExpr})
	// 	} else {
	// 		enumSpecFactMem, err := factMem.makeEnumSpecFactMem(pair.Stmt)
	// 		if err != nil {
	// 			return err
	// 		}
	// 		enumSpecFactMem.FactsINLogicExpr = append(enumSpecFactMem.FactsINLogicExpr, KnownSpecFact_InLogicExpr{pair.Stmt, pair.Indexes, logicExpr})
	// 	}
	// }

	// return nil
}

func (fact *KnownSpecFact_InLogicExpr) String() string {
	return fact.LogicExpr.String()
}

// func NewStoredSpecMemDictNode() *SpecFactMemItem {
// 	return &SpecFactMemItem{
// 		PureFacts: EnumSpecFactMem{
// 			Facts:            []KnownSpecFact{},
// 			FactsINLogicExpr: []KnownSpecFact_InLogicExpr{},
// 		},
// 		NotPureFacts: EnumSpecFactMem{
// 			Facts:            []KnownSpecFact{},
// 			FactsINLogicExpr: []KnownSpecFact_InLogicExpr{},
// 		},
// 		ExistFacts: EnumSpecFactMem{
// 			Facts:            []KnownSpecFact{},
// 			FactsINLogicExpr: []KnownSpecFact_InLogicExpr{},
// 		},
// 		NotExistFacts: EnumSpecFactMem{
// 			Facts:            []KnownSpecFact{},
// 			FactsINLogicExpr: []KnownSpecFact_InLogicExpr{},
// 		},
// 		Exist_St_Facts: EnumSpecFactMem{
// 			Facts:            []KnownSpecFact{},
// 			FactsINLogicExpr: []KnownSpecFact_InLogicExpr{},
// 		},
// 		NotExist_St_Facts: EnumSpecFactMem{
// 			Facts:            []KnownSpecFact{},
// 			FactsINLogicExpr: []KnownSpecFact_InLogicExpr{},
// 		},
// 	}
// }

// func NewStoredCondFuncMemDictNode() *StoredCondFuncMemDictNode {
// 	return &StoredCondFuncMemDictNode{
// 		PureFacts: StoredCondFuncMemDictNodeNode{
// 			Facts:            []StoredCondSpecFact{},
// 			FactsInLogicExpr: []StoredCondSpecFactUnderLogicExpr{},
// 		},
// 		NotPureFacts: StoredCondFuncMemDictNodeNode{
// 			Facts:            []StoredCondSpecFact{},
// 			FactsInLogicExpr: []StoredCondSpecFactUnderLogicExpr{},
// 		},
// 		ExistFacts: StoredCondFuncMemDictNodeNode{
// 			Facts:            []StoredCondSpecFact{},
// 			FactsInLogicExpr: []StoredCondSpecFactUnderLogicExpr{},
// 		},
// 		NotExistFacts: StoredCondFuncMemDictNodeNode{
// 			Facts:            []StoredCondSpecFact{},
// 			FactsInLogicExpr: []StoredCondSpecFactUnderLogicExpr{},
// 		},
// 		Exist_St_Facts: StoredCondFuncMemDictNodeNode{
// 			Facts:            []StoredCondSpecFact{},
// 			FactsInLogicExpr: []StoredCondSpecFactUnderLogicExpr{},
// 		},
// 		NotExist_St_Facts: StoredCondFuncMemDictNodeNode{
// 			Facts:            []StoredCondSpecFact{},
// 			FactsInLogicExpr: []StoredCondSpecFactUnderLogicExpr{},
// 		},
// 	}
// }

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

func (factMem *UniFactMem) insertFacts(uniStmt *ast.UniFactStmt, thenFacts []ast.FactStmt) error {
	for _, stmt := range thenFacts {
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

func NewPropMemory() *PropMem {
	return &PropMem{map[string]map[string]PropMemItem{}}
}
func NewFnMemory() *FnMem {
	return &FnMem{map[string]map[string]FnMemItem{}}
}

func NewObjMemory() *ObjMem {
	return &ObjMem{map[string]map[string]ObjMemItem{}}
}

func NewExistPropMemory() *ExistPropMem {
	return &ExistPropMem{map[string]map[string]ExistPropMemItem{}}
}

func (memory *PropMem) Insert(stmt *ast.DefConPropStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName]

	if !pkgExists {
		memory.Dict[pkgName] = make(map[string]PropMemItem)
		pkgMap = memory.Dict[pkgName]
	}

	node, nodeExists := pkgMap[stmt.DefHeader.Name]
	if !nodeExists {
		node = PropMemItem{stmt}
	}

	pkgMap[stmt.DefHeader.Name] = node

	return nil
}

func (memory *ObjMem) Insert(stmt *ast.DefObjStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName]

	if !pkgExists {
		memory.Dict[pkgName] = make(map[string]ObjMemItem)
		pkgMap = memory.Dict[pkgName]
	}

	for _, objName := range stmt.Objs {
		node, nodeExists := pkgMap[objName]
		if !nodeExists {
			node = ObjMemItem{stmt}
		}
		pkgMap[objName] = node
	}
	return nil
}

func (memory *FnMem) Insert(stmt *ast.DefConFnStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName]

	if !pkgExists {
		memory.Dict[pkgName] = make(map[string]FnMemItem)
		pkgMap = memory.Dict[pkgName]
	}

	node, nodeExists := pkgMap[stmt.DefHeader.Name]
	if !nodeExists {
		node = FnMemItem{stmt}
	}

	pkgMap[stmt.DefHeader.Name] = node

	return nil
}

func (memory *ExistPropMem) Insert(stmt *ast.DefConExistPropStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName]

	if !pkgExists {
		memory.Dict[pkgName] = make(map[string]ExistPropMemItem)
		pkgMap = memory.Dict[pkgName]
	}

	node, nodeExists := pkgMap[stmt.Def.DefHeader.Name]
	if !nodeExists {
		node = ExistPropMemItem{stmt}
	}
	pkgMap[stmt.Def.DefHeader.Name] = node

	return nil
}

func (memory *PropMem) Get(fc ast.FcAtom) (*ast.DefConPropStmt, bool) {
	pkgMap, pkgExists := memory.Dict[fc.PkgName]
	if !pkgExists {
		return nil, false
	}

	node, nodeExists := pkgMap[fc.Name]
	if !nodeExists {
		return nil, false
	}

	return node.Def, true
}

func (memory *ExistPropMem) Get(fc ast.FcAtom) (*ast.DefConExistPropStmt, bool) {
	pkgMap, pkgExists := memory.Dict[fc.PkgName]
	if !pkgExists {
		return nil, false
	}

	node, nodeExists := pkgMap[fc.Name]
	if !nodeExists {
		return nil, false
	}
	return node.Def, true
}

func (memory *FnMem) Get(fc ast.FcAtom) (*ast.DefConFnStmt, bool) {
	pkgMap, pkgExists := memory.Dict[fc.PkgName]
	if !pkgExists {
		return nil, false
	}

	node, nodeExists := pkgMap[fc.Name]
	if !nodeExists {
		return nil, false
	}
	return node.Def, true
}

func (memory *ObjMem) Get(fc ast.FcAtom) (*ast.DefObjStmt, bool) {
	pkgMap, pkgExists := memory.Dict[fc.PkgName]
	if !pkgExists {
		return nil, false
	}

	node, nodeExists := pkgMap[fc.Name]
	if !nodeExists {
		return nil, false
	}
	return node.Def, true
}
