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
	pkgMgr "golitex/package_manager"
)

type EnvPkgMgr struct {
	AbsPkgPathEnvMap map[string]*EnvMgr
	PkgMgr           *pkgMgr.PkgMgr
	// CurAbsRepoPath     string
	// CurDefaultPkgName string
}

// 为了确保实现上的简单性，不允许用重复的asPkgName
func (mgr *EnvPkgMgr) MergeGivenExecPkgMgr(absRepoPath string, asPkgName string, pkgEnv *EnvMgr) error {
	// if _, ok := mgr.AbsPkgPathEnvPairs[absRepoPath]; ok {
	// 	return fmt.Errorf("package already exists: %s", absRepoPath)
	// }

	storedPkgEnv := pkgEnv.RemoveBuiltinEnv()
	mgr.AbsPkgPathEnvMap[absRepoPath] = storedPkgEnv

	// // 使用 PathNameMgr 的方法添加包名和路径的映射
	// if err := mgr.AbsPathNameMgr.AddNamePath(asPkgName, absRepoPath); err != nil {
	// 	return err
	// }

	// // 把 curExec 的 pkgMgr 合并到现在的 pkgMgr 中
	// for pkgPath, pkgEnv := range pkgEnv.PkgMgr.AbsPkgPathEnvPairs {
	// 	if _, ok := mgr.AbsPkgPathEnvPairs[pkgPath]; ok {
	// 		continue
	// 	}
	// 	mgr.AbsPkgPathEnvPairs[pkgPath] = pkgEnv
	// }

	// // 使用 PathNameMgr 的 Merge 方法合并包名映射
	// if err := mgr.AbsPathNameMgr.Merge(pkgEnv.PkgMgr.AbsPathNameMgr); err != nil {
	// 	return err
	// }

	return nil
}

func NewPkgMgr(entranceRepoPath string, entranceDefaultPkgName string) *EnvPkgMgr {
	return &EnvPkgMgr{
		AbsPkgPathEnvMap: make(map[string]*EnvMgr),
		PkgMgr:           pkgMgr.NewEmptyPkgMgr(),
		// CurAbsRepoPath:     entranceRepoPath,
		// CurDefaultPkgName: entranceDefaultPkgName,
	}
}

func NewEnvPkgMgr(mgr *pkgMgr.PkgMgr) *EnvPkgMgr {
	return &EnvPkgMgr{
		AbsPkgPathEnvMap: make(map[string]*EnvMgr),
		PkgMgr:           mgr,
	}
}
