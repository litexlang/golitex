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
	glob "golitex/glob"
)

func (envMgr *EnvMgr) IsAtomNameDefinedByUser(AtomObjName string) bool {
	withPkgName, pkgName, _ := glob.GetPkgNameAndName(AtomObjName)

	if withPkgName && pkgName != envMgr.EnvPkgMgr.PkgMgr.CurPkgDefaultName {
		pkgEnvMgr := envMgr.GetEnvMgrOfPkgName(pkgName)
		if pkgEnvMgr == nil {
			return false
		}

		_, ok := pkgEnvMgr.AllDefinedAtomObjNames[AtomObjName]
		return ok
	} else {
		_, ok := envMgr.AllDefinedAtomObjNames[AtomObjName]
		return ok
	}
}

func (envMgr *EnvMgr) IsPropNameDefinedByUser(PropName string) bool {
	withPkgName, pkgName, _ := glob.GetPkgNameAndName(PropName)

	if withPkgName && pkgName != envMgr.EnvPkgMgr.PkgMgr.CurPkgDefaultName {
		pkgEnvMgr := envMgr.GetEnvMgrOfPkgName(pkgName)
		if pkgEnvMgr == nil {
			return false
		}

		_, ok := pkgEnvMgr.AllDefinedPropNames[PropName]
		return ok
	} else {
		_, ok := envMgr.AllDefinedPropNames[PropName]
		return ok
	}
}

func (envMgr *EnvMgr) IsExistPropNameDefinedByUser(ExistPropName string) bool {
	withPkgName, pkgName, _ := glob.GetPkgNameAndName(ExistPropName)

	if withPkgName && pkgName != envMgr.EnvPkgMgr.PkgMgr.CurPkgDefaultName {
		pkgEnvMgr := envMgr.GetEnvMgrOfPkgName(pkgName)
		if pkgEnvMgr == nil {
			return false
		}

		_, ok := pkgEnvMgr.AllDefinedExistPropNames[ExistPropName]
		return ok
	} else {
		_, ok := envMgr.AllDefinedExistPropNames[ExistPropName]
		return ok
	}
}

func (envMgr *EnvMgr) IsFnSetNameDefinedByUser(FnSetName string) bool {
	withPkgName, pkgName, _ := glob.GetPkgNameAndName(FnSetName)

	if withPkgName && pkgName != envMgr.EnvPkgMgr.PkgMgr.CurPkgDefaultName {
		pkgEnvMgr := envMgr.GetEnvMgrOfPkgName(pkgName)
		if pkgEnvMgr == nil {
			return false
		}

		_, ok := pkgEnvMgr.AllDefinedFnSetNames[FnSetName]
		return ok
	} else {
		_, ok := envMgr.AllDefinedFnSetNames[FnSetName]
		return ok
	}
}

func (envMgr *EnvMgr) IsAlgoNameDefinedByUser(AlgoName string) bool {
	withPkgName, pkgName, _ := glob.GetPkgNameAndName(AlgoName)

	if withPkgName && pkgName != envMgr.EnvPkgMgr.PkgMgr.CurPkgDefaultName {
		pkgEnvMgr := envMgr.GetEnvMgrOfPkgName(pkgName)
		if pkgEnvMgr == nil {
			return false
		}

		_, ok := pkgEnvMgr.AllDefinedAlgoNames[AlgoName]
		return ok
	} else {
		_, ok := envMgr.AllDefinedAlgoNames[AlgoName]
		return ok
	}
}

func (envMgr *EnvMgr) IsProveAlgoNameDefinedByUser(ProveAlgoName string) bool {
	withPkgName, pkgName, _ := glob.GetPkgNameAndName(ProveAlgoName)

	if withPkgName && pkgName != envMgr.EnvPkgMgr.PkgMgr.CurPkgDefaultName {
		pkgEnvMgr := envMgr.GetEnvMgrOfPkgName(pkgName)
		if pkgEnvMgr == nil {
			return false
		}

		_, ok := pkgEnvMgr.AllDefinedProveAlgoNames[ProveAlgoName]
		return ok
	} else {
		_, ok := envMgr.AllDefinedProveAlgoNames[ProveAlgoName]
		return ok
	}
}

func (envMgr *EnvMgr) IsPkgNameDefinedByUser(pkgName string) bool {
	_, ok := envMgr.EnvPkgMgr.PkgMgr.NameAbsPathMap[pkgName]
	return ok
}
