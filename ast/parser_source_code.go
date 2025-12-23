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
	glob "golitex/glob"
	"strings"
)

// * TODO: 在parse时，把pkgName改成当前项目里定义的 pkgName，而不是继续沿用原来的
// func ParseSourceCode(code string, pkgPathNameMgr *pkgMgr.PkgMgr) ([]Stmt, error) {
// 	blocks, err := PreprocessAndMakeSourceCodeIntoBlocks(code)
// 	if err != nil {
// 		return []Stmt{}, err
// 	}
// 	ret := []Stmt{}
// 	p := NewTbParser(pkgPathNameMgr)
// 	for _, block := range blocks {
// 		cur, err := p.Stmt(&block)
// 		if err != nil {
// 			return nil, err
// 		}
// 		ret = append(ret, cur)
// 	}

// 	return ret, nil
// }

func PreprocessSourceCode(code string) ([]string, error) {
	processedCode := strings.ReplaceAll(code, "\t", glob.Scope4Indents)
	processedCode = glob.RemoveWindowsCarriage(processedCode)
	lines := strings.Split(processedCode, "\n")
	return lines, nil
}

func PreprocessAndMakeSourceCodeIntoBlocks(code string) ([]tokenBlock, error) {
	preprocessedCodeLines, err := PreprocessSourceCode(code)
	if err != nil {
		return []tokenBlock{}, err
	}
	blocks, err := MakeTokenBlocks(preprocessedCodeLines)
	if err != nil {
		return []tokenBlock{}, err
	}
	return blocks, nil
}
