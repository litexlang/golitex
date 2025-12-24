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
)

// Helper methods for EnvMgr to access definitions

// 在def时，检查fact中的所有atom是否都定义了

func (envMgr *EnvMgr) IsNameUnavailable(name string, extraParams map[string]struct{}) glob.GlobRet {
	if envMgr.IsAtomNameDefinedByUser(name) || envMgr.IsPropNameDefinedByUser(name) || envMgr.IsExistPropNameDefinedByUser(name) || envMgr.IsFnSetNameDefinedByUser(name) || envMgr.IsAlgoNameDefinedByUser(name) || envMgr.IsProveAlgoNameDefinedByUser(name) || envMgr.IsPkgNameDefinedByUser(name) {
		return glob.NewEmptyGlobTrue()
	}

	if _, ok := extraParams[name]; ok {
		return glob.NewEmptyGlobTrue()
	}

	if glob.IsBuiltinName(name) {
		return glob.NewEmptyGlobTrue()
	}

	if _, ok := ast.IsNumLitAtomObj(ast.Atom(name)); ok {
		return glob.NewEmptyGlobTrue()
	}

	return glob.ErrRet(fmt.Errorf("undefined: %s", name))
}

func (envMgr *EnvMgr) IsValidAndAvailableName(name string) glob.GlobRet {
	err := glob.IsValidUseDefinedName(name)
	if err != nil {
		return glob.ErrRet(err)
	}

	defined := envMgr.IsNameUnavailable(name, map[string]struct{}{})
	if defined.IsNotTrue() {
		return glob.ErrRet(duplicateDefError(name))
	}

	return glob.NewEmptyGlobTrue()
}
