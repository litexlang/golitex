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

type PathNameMgr struct {
	NamePathMap    map[string]string
	PathNameSetMap map[string]map[string]struct{}
}

func NewPathNameMgr() *PathNameMgr {
	return &PathNameMgr{
		NamePathMap:    make(map[string]string),
		PathNameSetMap: make(map[string]map[string]struct{}),
	}
}

// HasName 检查包名是否已存在
func (mgr *PathNameMgr) HasName(name string) bool {
	_, ok := mgr.NamePathMap[name]
	return ok
}

// GetPathByName 根据包名获取路径
func (mgr *PathNameMgr) GetPathByName(name string) (string, bool) {
	path, ok := mgr.NamePathMap[name]
	return path, ok
}

// AddNamePath 添加包名到路径的映射，同时更新路径到包名集合的映射
func (mgr *PathNameMgr) AddNamePath(name, path string) error {
	if _, ok := mgr.NamePathMap[name]; ok {
		return fmt.Errorf("package name already exists: %s", name)
	}
	mgr.NamePathMap[name] = path

	// 同步更新 PathNameSetMap
	if _, ok := mgr.PathNameSetMap[path]; !ok {
		mgr.PathNameSetMap[path] = make(map[string]struct{})
	}
	// 检查是否已经存在，避免重复添加
	if _, ok := mgr.PathNameSetMap[path][name]; !ok {
		mgr.PathNameSetMap[path][name] = struct{}{}
	}

	return nil
}

// Merge 合并另一个 PathNameMgr 到当前 PathNameMgr
func (mgr *PathNameMgr) Merge(other *PathNameMgr) error {
	for name, path := range other.NamePathMap {
		if existingPath, ok := mgr.NamePathMap[name]; ok {
			if existingPath != path {
				return fmt.Errorf("package name %s refer to package %s, and package %s", name, path, existingPath)
			}
			// 如果包名已存在且路径相同，确保路径到包名集合的映射也更新了
			if _, ok := mgr.PathNameSetMap[path]; !ok {
				mgr.PathNameSetMap[path] = make(map[string]struct{})
			}
			if _, ok := mgr.PathNameSetMap[path][name]; !ok {
				mgr.PathNameSetMap[path][name] = struct{}{}
			}
			continue
		}
		// 包名不存在，直接添加
		if err := mgr.AddNamePath(name, path); err != nil {
			return err
		}
	}
	return nil
}
