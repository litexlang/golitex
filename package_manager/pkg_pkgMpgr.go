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

package litex_package_manager

import "fmt"

type AbsPathNameMgr struct {
	NameAbsPathMap        map[string]string
	AbsPathNamesSetMap    map[string]map[string]struct{}
	AbsPathDefaultNameMap map[string]string // 默认第一次看到某个path的时候，我们认为它的名字就是这个名字，后续如果出现其他名字，则认为这个path有多个名字，但是默认名字还是第一次知道它的时候它的名字
	CurPkgName            string
}

func NewPathNameMgr() *AbsPathNameMgr {
	return &AbsPathNameMgr{
		NameAbsPathMap:        make(map[string]string),
		AbsPathNamesSetMap:    make(map[string]map[string]struct{}),
		AbsPathDefaultNameMap: make(map[string]string),
		CurPkgName:            "",
	}
}

// AddNamePath 添加包名到路径的映射，同时更新路径到包名集合的映射
func (mgr *AbsPathNameMgr) AddNamePath(pkgName, pkgAbsPath string) error {
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

// Merge 合并另一个 PathNameMgr 到当前 PathNameMgr
func (mgr *AbsPathNameMgr) Merge(other *AbsPathNameMgr) error {
	for name, path := range other.NameAbsPathMap {
		if existingPath, ok := mgr.NameAbsPathMap[name]; ok {
			if existingPath != path {
				return fmt.Errorf("package name %s refer to package %s, and package %s", name, path, existingPath)
			}
			// 如果包名已存在且路径相同，确保路径到包名集合的映射也更新了
			if _, ok := mgr.AbsPathNamesSetMap[path]; !ok {
				mgr.AbsPathNamesSetMap[path] = make(map[string]struct{})
			}
			if _, ok := mgr.AbsPathNamesSetMap[path][name]; !ok {
				mgr.AbsPathNamesSetMap[path][name] = struct{}{}
			}
			continue
		}
		// 包名不存在，直接添加
		// if err := mgr.AddNamePath(name, path); err != nil {
		// 	return err
		// }
	}
	return nil
}

func (mgr *AbsPathNameMgr) GetDefaultPkgName(pkgName string) (string, error) {
	if pkgName == "" {
		return "", nil
	}

	path, ok := mgr.NameAbsPathMap[pkgName]
	if !ok {
		return pkgName, fmt.Errorf("package name %s not found", pkgName)
	}
	return mgr.AbsPathDefaultNameMap[path], nil
}
