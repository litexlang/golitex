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
	pkgMgr "golitex/package_manager"
)

type EnvPkgMgr struct {
	PkgPathEnvPairs map[string]*EnvMgr
	PkgPathNameMgr  *pkgMgr.PathNameMgr
}

// 为了确保实现上的简单性，不允许用重复的asPkgName
func (mgr *EnvPkgMgr) MergeGivenExecPkgMgr(importDirStmt *ast.ImportDirStmt, curEnv *EnvMgr) error {
	if _, ok := mgr.PkgPathEnvPairs[importDirStmt.Path]; ok {
		return fmt.Errorf("package already exists: %s", importDirStmt.Path)
	}
	mgr.PkgPathEnvPairs[importDirStmt.Path] = curEnv

	// 使用 PathNameMgr 的方法添加包名和路径的映射
	if err := mgr.PkgPathNameMgr.AddNamePath(importDirStmt.AsPkgName, importDirStmt.Path); err != nil {
		return err
	}

	// 把 curExec 的 pkgMgr 合并到现在的 pkgMgr 中
	for pkgPath, pkgEnv := range curEnv.PkgMgr.PkgPathEnvPairs {
		if _, ok := mgr.PkgPathEnvPairs[pkgPath]; ok {
			continue
		}
		mgr.PkgPathEnvPairs[pkgPath] = pkgEnv
	}

	// 使用 PathNameMgr 的 Merge 方法合并包名映射
	if err := mgr.PkgPathNameMgr.Merge(curEnv.PkgMgr.PkgPathNameMgr); err != nil {
		return err
	}

	return nil
}

func NewPackageManager() *EnvPkgMgr {
	return &EnvPkgMgr{
		PkgPathEnvPairs: make(map[string]*EnvMgr),
		PkgPathNameMgr:  pkgMgr.NewPathNameMgr(),
	}
}
