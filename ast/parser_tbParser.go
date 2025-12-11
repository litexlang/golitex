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

import pkgMgr "golitex/package_manager"

// TODO: 这里要让 parse obj 的时候，能读入 pkgName 这样parse的时候，自动把这个名字写成 defaultPkgName.name 的形式，就会很好，很方便我跨包引用，顺便能检查是否重复定义了
type TbParser struct {
	FreeParams                 map[string]struct{}
	PkgPathNameMgr             *pkgMgr.PathNameMgr
	CurPkgName                 string
	DefinedNamesAtEachParseEnv DefinedNameAtEachParseEnv
}

func NewTbParser(pkgPathNameMgr *pkgMgr.PathNameMgr) *TbParser {
	return &TbParser{
		FreeParams:                 make(map[string]struct{}),
		PkgPathNameMgr:             pkgPathNameMgr,
		CurPkgName:                 "",
		DefinedNamesAtEachParseEnv: NewDefinedNameAtEachParseEnv(),
	}
}

type DefinedNameAtEachParseEnv struct {
	Names []map[string]struct{}
}

func NewDefinedNameAtEachParseEnv() DefinedNameAtEachParseEnv {
	return DefinedNameAtEachParseEnv{
		Names: []map[string]struct{}{},
	}
}

func (p *TbParser) IsNameDefinedInCurrentPkg(name string) bool {
	for _, names := range p.DefinedNamesAtEachParseEnv.Names {
		if _, ok := names[name]; ok {
			return true
		}
	}
	return false
}

func (p *TbParser) DeleteCurrentParseEnv() {
	p.DefinedNamesAtEachParseEnv.Names = p.DefinedNamesAtEachParseEnv.Names[:len(p.DefinedNamesAtEachParseEnv.Names)-1]
}
