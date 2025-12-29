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
	pkgMgr "golitex/package_manager"
)

type EnvPkgMgr struct {
	AbsPkgPathEnvMgrMap map[string]*EnvMgr // import的包的envMgr永远只有一层 envFact。里面不包含builtin
	PkgMgr              *pkgMgr.PkgMgr
}

// func NewPkgMgr(entranceRepoPath string, entranceDefaultPkgName string) *EnvPkgMgr {
// 	return &EnvPkgMgr{
// 		AbsPkgPathEnvMgrMap: make(map[string]*EnvMgr),
// 		PkgMgr:              pkgMgr.NewEmptyPkgMgr(),
// 	}
// }

func NewEnvPkgMgr(mgr *pkgMgr.PkgMgr) *EnvPkgMgr {
	return &EnvPkgMgr{
		AbsPkgPathEnvMgrMap: make(map[string]*EnvMgr),
		PkgMgr:              mgr,
	}
}

func (envMgr *EnvMgr) GetEnvMgrOfName(name string) *EnvMgr {
	if name == envMgr.EnvPkgMgr.PkgMgr.CurPkgDefaultName {
		return envMgr
	}

	path := envMgr.EnvPkgMgr.PkgMgr.NameAbsPathMap[name]
	return envMgr.EnvPkgMgr.AbsPkgPathEnvMgrMap[path]
}
