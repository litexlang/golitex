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

package litex_ast

import pkgMgr "golitex/package_manager"

func ParseSourceCode_WhenCompileToLatex2(code string) ([]Stmt, error) {
	preprocessedCodeLines, err := PreprocessSourceCode(code)
	if err != nil {
		return []Stmt{}, err
	}

	blocks, err := MakeTokenBlocks(preprocessedCodeLines)
	if err != nil {
		return nil, err
	}

	ret := []Stmt{}
	pkgPathNameMgr := pkgMgr.NewEmptyPkgMgr("")
	p := NewTbParser(pkgPathNameMgr)
	for _, block := range blocks {
		cur, err := p.Stmt(&block)
		if err != nil {
			return nil, err
		}
		ret = append(ret, cur)
	}

	return ret, nil
}
