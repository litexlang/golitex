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
	ast "golitex/ast"
	taskManager "golitex/task_manager"
)

func (e *Env) GetLatestFnTemplate(fn ast.Fc) (*ast.FnTemplateStmt, bool) {
	fnAsAtom, isFnAsAtom := fn.(*ast.FcAtom)
	if !isFnAsAtom {
		return nil, false
	}

	for env := e; env != nil; env = env.Parent {
		fnDef, ok := env.FnSatisfyFnDefMem.Get(*fnAsAtom)
		if ok {
			// REMARK: 默认返回最后一个函数的定义
			return fnDef[len(fnDef)-1], true
		}
	}
	return nil, false
}

func (memory *FnInFnTemplateFactsMem) insert(name string, stmt *ast.FnTemplateStmt) error {
	pkgMap, pkgExists := memory.Dict[taskManager.CurrentPkg]

	if !pkgExists {
		memory.Dict[taskManager.CurrentPkg] = make(map[string]FnMemItem)
		pkgMap = memory.Dict[taskManager.CurrentPkg]
	}

	node, nodeExists := pkgMap[name]
	if !nodeExists {
		node = FnMemItem{[]*ast.FnTemplateStmt{stmt}}
	} else {
		node.Def = append(node.Def, stmt)
	}

	pkgMap[name] = node

	return nil
}
