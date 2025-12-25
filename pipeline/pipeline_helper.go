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
	ast "golitex/ast"
	glob "golitex/glob"
	packageMgr "golitex/package_manager"
	"path/filepath"
)

func absPathOfImportStmtPath(pkgMgr *packageMgr.PkgMgr, importStmt *ast.ImportDirStmt) (string, error) {
	var importRepoAbsPath string
	var err error

	// 分类：如果 importStmt 是import 全局的包，或者是import其他repo
	if importStmt.IsGlobalPkg {
		importRepoAbsPath, err = glob.GetGlobalPkgAbsPath(importStmt.AsPkgName)
		if err != nil {
			return "", err
		}
	} else {
		importRepoAbsPath = filepath.Join(pkgMgr.CurRepoAbsPath, importStmt.RelativePathOrGlobalPkgName)
	}

	return importRepoAbsPath, nil
}
