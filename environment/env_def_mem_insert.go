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

func (memory *PropDefMem) insert(stmt *ast.DefPropStmt) error {
	pkgMap, pkgExists := memory.Dict[taskManager.CurrentPkg]

	if !pkgExists {
		memory.Dict[taskManager.CurrentPkg] = make(map[string]PropMemItem)
		pkgMap = memory.Dict[taskManager.CurrentPkg]
	}

	node, nodeExists := pkgMap[stmt.DefHeader.Name]
	if !nodeExists {
		node = PropMemItem{stmt}
	}

	pkgMap[stmt.DefHeader.Name] = node

	return nil
}

func (memory *FnTemplateDefMem) insert(stmt *ast.DefFnTemplateStmt) error {
	pkgMap, pkgExists := memory.Dict[taskManager.CurrentPkg]

	if !pkgExists {
		memory.Dict[taskManager.CurrentPkg] = make(map[string]FnTemplateMemItem)
		pkgMap = memory.Dict[taskManager.CurrentPkg]
	}

	node, nodeExists := pkgMap[stmt.FnTemplateStmt.Name]
	if !nodeExists {
		node = FnTemplateMemItem{stmt}
	}
	pkgMap[stmt.FnTemplateStmt.Name] = node

	return nil
}

func (memory *ExistPropDefMem) insert(stmt *ast.DefExistPropStmt) error {
	pkgMap, pkgExists := memory.Dict[taskManager.CurrentPkg]

	if !pkgExists {
		memory.Dict[taskManager.CurrentPkg] = make(map[string]ExistPropMemItem)
		pkgMap = memory.Dict[taskManager.CurrentPkg]
	}

	node, nodeExists := pkgMap[stmt.DefBody.DefHeader.Name]
	if !nodeExists {
		node = ExistPropMemItem{stmt}
	}
	pkgMap[stmt.DefBody.DefHeader.Name] = node

	return nil
}

func (memory *ObjDefMem) insert(objName string) error {
	pkgMap, pkgExists := memory.Dict[taskManager.CurrentPkg]

	if !pkgExists {
		memory.Dict[taskManager.CurrentPkg] = make(map[string]ObjMemItem)
		pkgMap = memory.Dict[taskManager.CurrentPkg]
	}

	node, nodeExists := pkgMap[objName]
	if !nodeExists {
		node = ObjMemItem{nil}
	}

	pkgMap[objName] = node

	return nil
}
