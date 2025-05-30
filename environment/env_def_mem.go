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
	ast "golitex/ast"
	glob "golitex/glob"
)

type PropMemItem struct{ Def *ast.DefPropStmt }
type PropDefMem struct {
	Dict glob.Map2D[PropMemItem]
}

type ExistPropMemItem struct{ Def *ast.DefExistPropStmt }
type ExistPropDefMem struct {
	Dict glob.Map2D[ExistPropMemItem]
}

type ObjMemItem struct{ Def *ast.DefObjStmt }
type ObjDefMem struct {
	Dict glob.Map2D[ObjMemItem]
}

type FnMemItem struct{ Def *ast.DefFnStmt }
type FnDefMem struct {
	Dict glob.Map2D[FnMemItem]
}

type SetMemItem struct{ Def *ast.SetDefSetBuilderStmt }
type SetDefMem struct {
	Dict glob.Map2D[SetMemItem]
}

func newPropMemory() *PropDefMem {
	return &PropDefMem{make(glob.Map2D[PropMemItem])}
}
func newFnMemory() *FnDefMem {
	return &FnDefMem{make(glob.Map2D[FnMemItem])}
}

func newObjMemory() *ObjDefMem {
	return &ObjDefMem{make(glob.Map2D[ObjMemItem])}
}

func newExistPropMemory() *ExistPropDefMem {
	return &ExistPropDefMem{make(glob.Map2D[ExistPropMemItem])}
}

// func newSetMemory() *SetDefMem {
// 	return &SetDefMem{make(glob.Map2D[SetMemItem])}
// }
