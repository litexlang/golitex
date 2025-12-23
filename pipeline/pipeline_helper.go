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
