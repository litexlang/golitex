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
	glob "golitex/glob"
)

func (envMgr *EnvMgr) IsNameUnavailable(name string, extraParams map[string]struct{}) bool {
	if _, ok := extraParams[name]; ok {
		return true
	}

	if glob.IsBuiltinName(name) {
		return true
	}

	if envMgr.IsAtomNameDefinedByUser(name) || envMgr.IsPropNameDefinedByUser(name) || envMgr.IsFnSetNameDefinedByUser(name) || envMgr.IsAlgoNameDefinedByUser(name) || envMgr.IsProveAlgoNameDefinedByUser(name) || envMgr.IsPkgNameDefinedByUser(name) || envMgr.IsFnNameDefinedByUser(name) {
		// ||envMgr.IsExistPropNameDefinedByUser(name){
		return true
	}

	return false
}

func (envMgr *EnvMgr) IsValidAndAvailableName(name string) bool {
	err := glob.IsValidUseDefinedName(name)
	if err != nil {
		return false
	}

	defined := envMgr.IsNameUnavailable(name, map[string]struct{}{})
	if defined {
		return false
	}

	return true
}
