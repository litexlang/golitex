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

package litex_pipeline

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	pkgMgr "golitex/package_manager"
	"os"
	"strings"
)

func FormatCode(path string) (glob.GlobRet, error) {
	content, err := os.ReadFile(path)
	if err != nil {
		return glob.NewGlobErr(fmt.Sprintf("failed to read file %s: %s", path, err.Error())), err
	}

	pkgPathNameMgr := pkgMgr.NewEmptyPkgMgr()

	blocks, err := ast.PreprocessAndMakeSourceCodeIntoBlocks(string(content))
	if err != nil {
		return glob.NewGlobErr(err.Error()), err
	}

	p := ast.NewTbParser(pkgPathNameMgr)
	stmtStrSlice := []string{}
	for _, block := range blocks {
		topStmt, err := p.Stmt(&block)
		if err != nil {
			return glob.NewGlobErr(err.Error()), err
		}
		stmtStrSlice = append(stmtStrSlice, topStmt.String())
	}

	// 把 code 写到 path 里
	err = os.WriteFile(path, []byte((strings.Join(stmtStrSlice, "\n\n"))), 0644)
	if err != nil {
		return glob.NewGlobErr(fmt.Sprintf("failed to write file %s: %s", path, err.Error())), err
	}
	return glob.NewGlobTrue(fmt.Sprintf("formatted code written to %s", path)), nil
}
