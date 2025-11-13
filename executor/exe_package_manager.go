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

package litex_executor

import (
	"fmt"
	env "golitex/environment"
)

type PackageManager struct {
	PkgEnvMap map[string]*env.Env
}

func (pkgMgr *PackageManager) NewPkgEnvPair(pkgName string, pkgEnv *env.Env) error {
	if _, ok := pkgMgr.PkgEnvMap[pkgName]; ok {
		return fmt.Errorf("package name already exists: %s", pkgName)
	}
	pkgMgr.PkgEnvMap[pkgName] = pkgEnv
	return nil
}

func NewPackageManager() *PackageManager {
	return &PackageManager{
		PkgEnvMap: make(map[string]*env.Env),
	}
}
