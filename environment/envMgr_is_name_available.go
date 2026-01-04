// Copyright Jiachen Shen.
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
	glob "golitex/glob"
)

func (envMgr *EnvMgr) IsNameUnavailable(name string, extraParams map[string]struct{}) *glob.StmtRet {
	if _, ok := extraParams[name]; ok {
		return glob.NewEmptyStmtTrue()
	}

	if glob.IsBuiltinName(name) {
		return glob.NewEmptyStmtTrue()
	}

	if envMgr.IsAtomNameDefinedByUser(name) || envMgr.IsPropNameDefinedByUser(name) || envMgr.IsFnSetNameDefinedByUser(name) || envMgr.IsAlgoNameDefinedByUser(name) || envMgr.IsProveAlgoNameDefinedByUser(name) || envMgr.IsPkgNameDefinedByUser(name) {
		// ||envMgr.IsExistPropNameDefinedByUser(name){
		return glob.NewEmptyStmtTrue()
	}

	return glob.ErrRet(fmt.Sprintf("undefined: %s", name))
}

func (envMgr *EnvMgr) IsValidAndAvailableName(name string) *glob.StmtRet {
	err := glob.IsValidUseDefinedName(name)
	if err != nil {
		return glob.ErrRetWithErr(err)
	}

	defined := envMgr.IsNameUnavailable(name, map[string]struct{}{})
	if defined.IsTrue() {
		return glob.ErrRetWithErr(duplicateDefError(name))
	}

	return glob.NewEmptyStmtTrue()
}
