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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"slices"
)

func (envMgr *EnvMgr) curEnvDepth() int {
	return len(envMgr.EnvSlice) - 1
}

func (envMgr *EnvMgr) CurEnv() *EnvMemory {
	return &envMgr.EnvSlice[len(envMgr.EnvSlice)-1]
}

func (envMgr *EnvMgr) NewDefProp_BuiltinProp(stmt *ast.DefPropStmt) glob.GlobRet {
	// prop名不能和parameter名重叠
	if slices.Contains(stmt.DefHeader.Params, string(stmt.DefHeader.Name)) {
		return glob.ErrRet(fmt.Errorf("prop name %s cannot be the same as parameter name %s", stmt.DefHeader.Name, stmt.DefHeader.Name))
	}

	ret := envMgr.IsValidIdentifierAvailable(string(stmt.DefHeader.Name))
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue("")
}
