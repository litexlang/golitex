package litex_pipeline

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
	packageMgr "golitex/package_manager"
	"path/filepath"
)

// return: new imported pkg, new envMgr, globRet
func RunImport(pkgMgr *packageMgr.AbsPathNameMgr, importStmt *ast.ImportDirStmt) (bool, *env.EnvMgr, glob.GlobRet) {
	var absPathOfImportedRepo string
	var err error

	if importStmt.IsGlobalPkg {
		absPathOfImportedRepo, err = glob.GetGlobalPkgAbsPath(importStmt.AsPkgName)
		if err != nil {
			return false, nil, glob.NewGlobErr(err.Error())
		}
	} else {
		absPathOfImportedRepo = filepath.Join(pkgMgr.CurRepoAbsPath, importStmt.RelativePathOrGlobalPkgName)
	}

	// 这个repo已经被引用过了
	if _, ok := pkgMgr.AbsPathDefaultNameMap[absPathOfImportedRepo]; ok {
		path, ok := pkgMgr.NameAbsPathMap[importStmt.AsPkgName]
		// 这个 name 没有被使用过
		if !ok {
			pkgMgr.NameAbsPathMap[importStmt.AsPkgName] = absPathOfImportedRepo
			pkgMgr.AbsPathNamesSetMap[absPathOfImportedRepo][importStmt.AsPkgName] = struct{}{}

			return false, nil, glob.NewGlobTrue(fmt.Sprintf("%s\n", importStmt))
		} else {
			// 这个name已经用过了，需要验证一下是不是之前对应的也是目前的abs path
			if path != absPathOfImportedRepo {
				return false, nil, glob.NewGlobErr(fmt.Sprintf("error at %s:\npackage name %s is already used for repository %s, it can not be name for %s", importStmt, importStmt.AsPkgName, path, absPathOfImportedRepo))
			}
		}
	}

	// 这个repo没被引用过

	envPkgMgr := env.NewEnvPkgMgrWithPkgMgr(pkgMgr)
	envMgr, err := NewBuiltinEnvMgr(envPkgMgr)
	if err != nil {
		return false, nil, glob.NewGlobErr(err.Error())
	}

	return true, envMgr, glob.NewGlobTrue(fmt.Sprintf("%s\n", importStmt))
}
