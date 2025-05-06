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

import ast "golitex/litex_ast"

type PropMemItem struct{ Def *ast.DefConPropStmt }
type PropMem struct {
	Dict map[string]map[string]PropMemItem
}

type ExistPropMemItem struct{ Def *ast.DefConExistPropStmt }
type ExistPropMem struct {
	Dict map[string]map[string]ExistPropMemItem
}

type ObjMemItem struct{ Def *ast.DefObjStmt }
type ObjMem struct {
	Dict map[string]map[string]ObjMemItem
}

type FnMemItem struct{ Def *ast.DefConFnStmt }
type FnMem struct {
	Dict map[string]map[string]FnMemItem
}

type EmitWhenSpecFactIsTrueMem struct {
	Dict map[string]map[string][]EmitWhenSpecFactIsTrueMemItem
}

type EmitWhenSpecFactIsTrueMemItem struct {
	Params []string
	Facts  []ast.FactStmt
}
