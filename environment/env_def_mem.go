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
)

type PropMemItem struct {
	Def *ast.DefPropStmt
}
type PropDefMem struct {
	Dict map[string]PropMemItem
}

type ExistPropMemItem struct{ Def *ast.DefExistPropStmt }
type ExistPropDefMem struct {
	Dict map[string]ExistPropMemItem
}

// type FnTemplateMemItem struct{ Def *ast.DefFnTemplateStmt }

// type FnTemplateDefMem struct {
// 	Dict map[string]FnTemplateMemItem
// }

type FnTemplateDefMem map[string]ast.DefFnTemplateStmt

type ObjMemItem struct{ Def *ast.DefObjStmt }
type ObjDefMem struct {
	Dict map[string]ObjMemItem
}

type FnInFnTemplateFactsMem map[string][]*ast.FnTemplateStmt

func newPropMemory() *PropDefMem {
	return &PropDefMem{make(map[string]PropMemItem)}
}
func newFnMemory() FnInFnTemplateFactsMem {
	return make(FnInFnTemplateFactsMem)
}

func newObjMemory() *ObjDefMem {
	return &ObjDefMem{make(map[string]ObjMemItem)}
}

func newExistPropMemory() *ExistPropDefMem {
	return &ExistPropDefMem{make(map[string]ExistPropMemItem)}
}

// func newFnTemplateMemory() *FnTemplateDefMem {
// 	return &FnTemplateDefMem{make(map[string]FnTemplateMemItem)}
// }

// func newFnTemplateMemory() FnTemplateDefMem {
// 	return make(FnTemplateDefMem)
// }
