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

package litex_ast

import (
	"fmt"
	pkgMgr "golitex/package_manager"
)

// TODO: 这里要让 parse obj 的时候，能读入 pkgName 这样parse的时候，自动把这个名字写成 defaultPkgName.name 的形式，就会很好 =，很方便我跨包引用，顺便能检查是否重复定义了
type TbParser struct {
	FreeParams                    map[string]struct{}
	PkgPathNameMgr                *pkgMgr.AbsPathNameMgr
	CurPkgPath                    string
	DefinedNamesAtEachParseEnv    DefinedNameAtEachParseEnv
	AllDefinedNamesExceptPkgNames map[string]struct{}
}

func NewTbParser(curPkgName string, pkgPathNameMgr *pkgMgr.AbsPathNameMgr) *TbParser {
	return &TbParser{
		FreeParams:                    make(map[string]struct{}),
		PkgPathNameMgr:                pkgPathNameMgr,
		CurPkgPath:                    curPkgName,
		DefinedNamesAtEachParseEnv:    NewDefinedNameAtEachParseEnv(),
		AllDefinedNamesExceptPkgNames: make(map[string]struct{}),
	}
}

type DefinedNameAtEachParseEnv struct {
	Names []map[string]struct{}
}

func NewDefinedNameAtEachParseEnv() DefinedNameAtEachParseEnv {
	return DefinedNameAtEachParseEnv{
		Names: []map[string]struct{}{make(map[string]struct{})},
	}
}

func (p *TbParser) IsNameDefinedInCurrentParseEnv(name string) bool {
	_, ok := p.AllDefinedNamesExceptPkgNames[name]
	if ok {
		return true
	}
	if _, ok := p.PkgPathNameMgr.NameAbsPathMap[name]; ok {
		return true
	}
	return false
}

func (p *TbParser) NewParseEnv() {
	p.DefinedNamesAtEachParseEnv.Names = append(p.DefinedNamesAtEachParseEnv.Names, make(map[string]struct{}))
}

func (p *TbParser) NewDefinedNameInCurrentParseEnv(name string) error {
	if _, ok := p.AllDefinedNamesExceptPkgNames[name]; ok {
		return fmt.Errorf("name %s is already defined", name)
	}
	p.AllDefinedNamesExceptPkgNames[name] = struct{}{}
	p.DefinedNamesAtEachParseEnv.Names[len(p.DefinedNamesAtEachParseEnv.Names)-1][name] = struct{}{}
	return nil
}

func (p *TbParser) DeleteCurrentParseEnv() {
	if len(p.DefinedNamesAtEachParseEnv.Names) <= 1 {
		return // Don't delete the last ParseEnv to prevent empty slice
	}
	for name := range p.DefinedNamesAtEachParseEnv.Names[len(p.DefinedNamesAtEachParseEnv.Names)-1] {
		delete(p.AllDefinedNamesExceptPkgNames, name)
	}
	p.DefinedNamesAtEachParseEnv.Names = p.DefinedNamesAtEachParseEnv.Names[:len(p.DefinedNamesAtEachParseEnv.Names)-1]
}
