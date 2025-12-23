package litex_pipeline

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	exe "golitex/executor"
	glob "golitex/glob"
	packageMgr "golitex/package_manager"
	"os"
	"path/filepath"
	"strings"
)

// return: new imported pkg, new envMgr, globRet
func RunImport(pkgMgr *packageMgr.AbsPathNameMgr, importStmt *ast.ImportDirStmt) (bool, *env.EnvMgr, glob.GlobRet) {
	var importRepoAbsPath string
	var err error

	// 分类：如果 importStmt 是import 全局的包，或者是import其他repo
	if importStmt.IsGlobalPkg {
		importRepoAbsPath, err = glob.GetGlobalPkgAbsPath(importStmt.AsPkgName)
		if err != nil {
			return false, nil, glob.NewGlobErr(err.Error())
		}
	} else {
		importRepoAbsPath = filepath.Join(pkgMgr.CurRepoAbsPath, importStmt.RelativePathOrGlobalPkgName)
	}

	// 这个repo已经被引用过了
	if _, ok := pkgMgr.AbsPathDefaultNameMap[importRepoAbsPath]; ok {
		path, ok := pkgMgr.NameAbsPathMap[importStmt.AsPkgName]
		// 这个 name 没有被使用过
		if !ok {
			pkgMgr.NameAbsPathMap[importStmt.AsPkgName] = importRepoAbsPath
			pkgMgr.AbsPathNamesSetMap[importRepoAbsPath][importStmt.AsPkgName] = struct{}{}

			return false, nil, glob.NewGlobTrue(fmt.Sprintf("%s\n", importStmt))
		} else {
			// 这个name已经用过了，需要验证一下是不是之前对应的也是目前的abs path
			if path != importRepoAbsPath {
				return false, nil, glob.NewGlobErr(fmt.Sprintf("error at %s:\npackage name %s is already used for repository %s, it can not be name for %s", importStmt, importStmt.AsPkgName, path, importRepoAbsPath))
			}
		}
	}

	// 把这个包存在 pkgMgr 里
	pkgMgr.NameAbsPathMap[importStmt.AsPkgName] = importRepoAbsPath
	pkgMgr.AbsPathNamesSetMap[importRepoAbsPath][importStmt.AsPkgName] = struct{}{}
	pkgMgr.AbsPathDefaultNameMap[importRepoAbsPath] = importStmt.AsPkgName

	// 这个repo还没被引用，那么就第一次运行它
	envMgr, ret := RunFileWithPkgMgr(importRepoAbsPath, filepath.Join(importRepoAbsPath, glob.MainDotLit), importStmt.AsPkgName, pkgMgr)
	if ret.IsNotTrue() {
		return false, nil, ret
	}

	return true, envMgr, glob.NewGlobTrue(fmt.Sprintf("%s\n", importStmt))
}

func RunFileWithPkgMgr(fileRepoAbsPath string, fileAbsPath string, curPkgName string, pkgMgr *packageMgr.AbsPathNameMgr) (*env.EnvMgr, glob.GlobRet) {
	// 更新 current working repo
	previousCurRepoAbsPath := pkgMgr.CurRepoAbsPath
	previousCurPkgDefaultName := pkgMgr.CurPkgDefaultName
	pkgMgr.CurRepoAbsPath = fileRepoAbsPath
	pkgMgr.CurPkgDefaultName = curPkgName

	defer func() {
		pkgMgr.CurRepoAbsPath = previousCurRepoAbsPath
		pkgMgr.CurPkgDefaultName = previousCurPkgDefaultName
	}()

	envPkgMgr := env.NewEnvPkgMgrWithPkgMgr(pkgMgr)
	envMgr, err := NewBuiltinEnvMgr(envPkgMgr)
	if err != nil {
		return nil, glob.NewGlobErr(err.Error())
	}

	// 获得那个 main.lit
	code, err := os.ReadFile(fileAbsPath)
	if err != nil {
		return nil, glob.NewGlobErr(err.Error())
	}

	stmtSlice, err := ast.ParseSourceCode(string(code), pkgMgr.CurPkgDefaultName, pkgMgr, pkgMgr.CurRepoAbsPath)
	if err != nil {
		return nil, glob.NewGlobErr(err.Error())
	}

	curExec := exe.NewExecutor(envMgr)

	msgs := []string{}
	for _, topStmt := range stmtSlice {
		ret := RunStmtAndImportStmtInExecutor(curExec, topStmt)
		msgs = append(msgs, ret.String())

		if ret.IsNotTrue() {
			return nil, glob.NewGlobErr(strings.Join(msgs, "\n"))
		}
	}

	envMgrWithoutBuiltinLogic := envMgr.RemoveBuiltinEnv()

	return envMgrWithoutBuiltinLogic, glob.NewGlobTrue(strings.Join(msgs, "\n"))
}
