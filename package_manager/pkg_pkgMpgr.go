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

package litex_package_manager

import (
	"fmt"
)

type PkgMgr struct {
	NameAbsPathMap     map[string]string
	AbsPathNamesSetMap map[string]map[string]struct{}
	// 默认第一次看到某个path的时候，我们认为它的名字就是这个名字，后续如果出现其他名字，则认为这个path有多个名字，但是默认名字还是第一次知道它的时候它的名字
	AbsPathDefaultNameMap map[string]string
	CurPkgDefaultName     string // Empty when REPL or in main runtime
	CurRepoAbsPath        string

	EntranceAbsPath string
}

func (mgr *PkgMgr) GetDefaultNameOfPkgName(name string) (string, error) {
	path, ok := mgr.NameAbsPathMap[name]
	if !ok {
		return "", fmt.Errorf("%s is not a defined package name", name)
	}

	pkgName, ok := mgr.AbsPathDefaultNameMap[path]
	if !ok {
		return "", fmt.Errorf("%s is not imported", path)
	}

	return pkgName, nil
}

func (mgr *PkgMgr) IsREPL() bool {
	return mgr.CurPkgDefaultName == ""
}

func NewEmptyPkgMgr(entranceAbsPath string) *PkgMgr {
	return &PkgMgr{
		NameAbsPathMap:        make(map[string]string),
		AbsPathNamesSetMap:    make(map[string]map[string]struct{}),
		AbsPathDefaultNameMap: make(map[string]string),
		CurPkgDefaultName:     "",
		CurRepoAbsPath:        "",
		EntranceAbsPath:       entranceAbsPath,
	}
}

// AddNamePath 添加包名到路径的映射，同时更新路径到包名集合的映射
func (mgr *PkgMgr) AddNamePath(pkgName, pkgAbsPath string) error {
	if _, ok := mgr.NameAbsPathMap[pkgName]; ok {
		return fmt.Errorf("package name already exists: %s, but it is used as package name for package %s", pkgName, mgr.NameAbsPathMap[pkgName])
	}
	mgr.NameAbsPathMap[pkgName] = pkgAbsPath

	// 同步更新 PathNameSetMap
	if _, ok := mgr.AbsPathNamesSetMap[pkgAbsPath]; !ok {
		mgr.AbsPathNamesSetMap[pkgAbsPath] = make(map[string]struct{})
		mgr.AbsPathDefaultNameMap[pkgAbsPath] = pkgName
	}
	// 检查是否已经存在，避免重复添加
	if _, ok := mgr.AbsPathNamesSetMap[pkgAbsPath][pkgName]; !ok {
		mgr.AbsPathNamesSetMap[pkgAbsPath][pkgName] = struct{}{}
	}

	return nil
}
