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
	ast "golitex/ast"
	env "golitex/environment"
)

type PackageManager struct {
	PkgEnvPairs         map[string]*env.Env
	PkgNamePkgPathPairs map[string]string
}

func (pkgMgr *PackageManager) NewPkgEnvPair(importDirStmt *ast.ImportDirStmt, pkgEnv *env.Env) error {
	if _, ok := pkgMgr.PkgEnvPairs[importDirStmt.Path]; ok {
		return fmt.Errorf("package already exists: %s", importDirStmt.Path)
	}
	pkgMgr.PkgEnvPairs[importDirStmt.Path] = pkgEnv
	pkgMgr.PkgNamePkgPathPairs[importDirStmt.AsPkgName] = importDirStmt.Path
	return nil
}

func NewPackageManager() *PackageManager {
	return &PackageManager{
		PkgEnvPairs:         make(map[string]*env.Env),
		PkgNamePkgPathPairs: make(map[string]string),
	}
}
