// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_memory

import ast "golitex/litex_ast"

func NewSpecFactMemDict() *SpecFactMemDict {
	return &SpecFactMemDict{map[string]map[string]StoredSpecMemDictNode{}}
}

func (factMem *SpecFactMemDict) Insert(stmt *ast.SpecFactStmt) error {
	pkgMap, pkgExists := factMem.Dict[stmt.PropName.PkgName] // 检查 pkgName 是否存在

	// 如果包不存在，初始化包映射
	if !pkgExists {
		factMem.Dict[stmt.PropName.PkgName] = make(map[string]StoredSpecMemDictNode)
		pkgMap = factMem.Dict[stmt.PropName.PkgName]
	}

	// 获取或创建节点
	node, nodeExists := pkgMap[stmt.PropName.Value]
	if !nodeExists {
		node = StoredSpecMemDictNode{
			Facts: []StoredSpecFact{},
		}
	}

	// 添加新事实
	if stmt.IsTrue {
		node.Facts = append(node.Facts, StoredSpecFact{stmt.IsTrue, stmt.Params})
	} else {
		node.NotFacts = append(node.NotFacts, StoredSpecFact{stmt.IsTrue, stmt.Params})
	}

	// 更新映射中的节点
	pkgMap[stmt.PropName.Value] = node

	return nil
}

func (factMem *SpecFactMemDict) GetNode(stmt *ast.SpecFactStmt) ([]StoredSpecFact, bool) {
	pkgMap, pkgExists := factMem.Dict[stmt.PropName.PkgName] // 检查 pkgName 是否存在
	if !pkgExists {
		return nil, false // 返回零值
	}
	node, nodeExists := pkgMap[stmt.PropName.Value] // 检查 value 是否存在
	if !nodeExists {
		return nil, false // 返回零值
	}

	if stmt.IsTrue {
		return node.Facts, true
	} else {
		return node.NotFacts, true
	}
}

func NewCondFactMemDict() *CondFactMemDict {
	return &CondFactMemDict{map[string]map[string]StoredCondFuncMemDictNode{}}
}

func (factMem *CondFactMemDict) Insert(condStmt *ast.CondFactStmt) error {
	for _, stmt := range condStmt.ThenFacts {
		err := factMem.InsertSpecFact(condStmt, stmt)
		if err != nil {
			return err
		}
	}
	return nil
}

func (factMem *CondFactMemDict) InsertSpecFact(condStmt *ast.CondFactStmt, stmt *ast.SpecFactStmt) error {
	// 检查 pkgName 是否存在，不存在则初始化
	pkgName := stmt.PropName.PkgName
	optName := stmt.PropName.Value

	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
		factMem.SpecFactsDict[pkgName] = make(map[string]StoredCondFuncMemDictNode)
	}

	// 获取或初始化节点
	node, nodeExists := factMem.SpecFactsDict[pkgName][optName]
	if !nodeExists {
		node = StoredCondFuncMemDictNode{
			Facts: []StoredCondSpecFact{},
		}
	}

	if stmt.IsTrue {
		node.Facts = append(node.Facts, StoredCondSpecFact{stmt.IsTrue, stmt.Params, condStmt})
	} else {
		node.NotFacts = append(node.NotFacts, StoredCondSpecFact{stmt.IsTrue, stmt.Params, condStmt})
	}

	// 更新回字典
	factMem.SpecFactsDict[pkgName][optName] = node
	return nil
}

func (factMem *CondFactMemDict) GetSpecFactNode(stmt *ast.SpecFactStmt) ([]StoredCondSpecFact, bool) {
	pkgName := stmt.PropName.PkgName
	optName := stmt.PropName.Value

	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
		return []StoredCondSpecFact{}, false
	}

	if storedFacts, optExists := factMem.SpecFactsDict[pkgName][optName]; !optExists {
		return []StoredCondSpecFact{}, false
	} else {
		if stmt.IsTrue {
			return storedFacts.Facts, true
		} else {
			return storedFacts.NotFacts, true
		}
	}
}

func (factMem *UniFactMemDict) Insert(fact *ast.ConUniFactStmt) error {
	for _, stmt := range fact.ThenFacts {
		err := factMem.insertSpecFact(fact, stmt)
		if err != nil {
			return err
		}
	}
	return nil
}

func (factMem *UniFactMemDict) insertSpecFact(uniStmt *ast.ConUniFactStmt, stmt *ast.SpecFactStmt) error {
	// 检查 pkgName 是否存在，不存在则初始化
	pkgName := stmt.PropName.PkgName
	optName := stmt.PropName.Value

	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
		factMem.SpecFactsDict[pkgName] = make(map[string]StoredUniFuncMemDictNode)
	}

	// 获取或初始化节点
	node, nodeExists := factMem.SpecFactsDict[pkgName][optName]
	if !nodeExists {
		node = StoredUniFuncMemDictNode{
			Facts: []StoredUniSpecFact{},
		}
	}

	if stmt.IsTrue {
		node.Facts = append(node.Facts, StoredUniSpecFact{stmt.IsTrue, &stmt.Params, uniStmt})
	} else {
		node.NotFacts = append(node.NotFacts, StoredUniSpecFact{stmt.IsTrue, &stmt.Params, uniStmt})
	}

	// 更新回字典
	factMem.SpecFactsDict[pkgName][optName] = node
	return nil
}

func NewUniFactMemDict() *UniFactMemDict {
	return &UniFactMemDict{map[string]map[string]StoredUniFuncMemDictNode{}}
}

func (factMem *UniFactMemDict) GetSpecFactNodeWithTheSameIsTrue(stmt *ast.SpecFactStmt) ([]StoredUniSpecFact, bool) {
	pkgName := stmt.PropName.PkgName
	optName := stmt.PropName.Value

	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
		return []StoredUniSpecFact{}, false
	}

	if storedFacts, optExists := factMem.SpecFactsDict[pkgName][optName]; !optExists {
		return []StoredUniSpecFact{}, false
	} else {
		if stmt.IsTrue {
			return storedFacts.Facts, true
		} else {
			return storedFacts.NotFacts, true
		}
	}
}
