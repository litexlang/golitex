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

type FnTemplateMemItem struct{ Def *ast.FnTemplateDefStmt }
type FnTemplateDefMem struct {
	Dict glob.Map2D[FnTemplateMemItem]
}

type ObjMemItem struct{ Def *ast.DefObjStmt }
type ObjDefMem struct {
	Dict glob.Map2D[ObjMemItem]
}

type FnMemItem struct{ Def *ast.DefFnStmt }
type FnDefMem struct {
	Dict glob.Map2D[FnMemItem]
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

func newFnTemplateMemory() *FnTemplateDefMem {
	return &FnTemplateDefMem{make(glob.Map2D[FnTemplateMemItem])}
}
