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
	PkgPathEnvPairs     map[string]*env.Env
	PkgNamePkgPathPairs map[string]string
}

// 为了确保实现上的简单性，不允许用重复的asPkgName
func (pkgMgr *PackageManager) MergeGivenExecPkgMgr(importDirStmt *ast.ImportDirStmt, curExec *Executor) error {
	if _, ok := pkgMgr.PkgPathEnvPairs[importDirStmt.Path]; ok {
		return fmt.Errorf("package already exists: %s", importDirStmt.Path)
	}
	pkgMgr.PkgPathEnvPairs[importDirStmt.Path] = curExec.Env

	if _, ok := pkgMgr.PkgNamePkgPathPairs[importDirStmt.AsPkgName]; ok {
		return fmt.Errorf("package name already exists: %s", importDirStmt.AsPkgName)
	}
	pkgMgr.PkgNamePkgPathPairs[importDirStmt.AsPkgName] = importDirStmt.Path

	// 把 curExec 的 pkgMgr 合并到现在的 pkgMgr 中
	for pkgPath, pkgEnv := range curExec.PkgMgr.PkgPathEnvPairs {
		if _, ok := pkgMgr.PkgPathEnvPairs[pkgPath]; ok {
			continue
		}
		pkgMgr.PkgPathEnvPairs[pkgPath] = pkgEnv
	}
	for pkgName, pkgPath := range curExec.PkgMgr.PkgNamePkgPathPairs {
		if path, ok := pkgMgr.PkgNamePkgPathPairs[pkgName]; ok {
			if path != pkgPath {
				return fmt.Errorf("package name %s refer to package %s, and package %s", pkgName, pkgPath, path)
			}
		}
		curExec.PkgMgr.PkgNamePkgPathPairs[pkgName] = pkgPath
	}

	return nil
}

func NewPackageManager() *PackageManager {
	return &PackageManager{
		PkgPathEnvPairs:     make(map[string]*env.Env),
		PkgNamePkgPathPairs: make(map[string]string),
	}
}
