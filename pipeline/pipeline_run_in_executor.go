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
	env "golitex/environment"
	exe "golitex/executor"
	glob "golitex/glob"
	packageMgr "golitex/package_manager"
	"os"
	"path/filepath"
)

func RunStmtInExecutor(curExec *exe.Executor, stmt ast.Stmt) *glob.StmtRet {
	switch asStmt := stmt.(type) {
	case *ast.RunFileStmt:
		return RunFileStmtInExecutor(curExec, asStmt)
	case *ast.ImportDirStmt:
		return RunImportStmtInExecutor(curExec, asStmt)
	default:
		return curExec.Stmt(asStmt)
	}
}

func RunFileStmtInExecutor(curExec *exe.Executor, importFileStmt *ast.RunFileStmt) *glob.StmtRet {
	// 把 entrance repo path 和 importFileStmt.Path结合起来
	path := filepath.Join(curExec.Env.EnvPkgMgr.PkgMgr.CurRepoAbsPath, importFileStmt.Path)

	content, err := os.ReadFile(path)
	if err != nil {
		return glob.ErrRet(err.Error())
	}
	code := string(content)

	// stmtSlice, err := ast.ParseSourceCode(code, curExec.Env.EnvPkgMgr.PkgMgr)
	// if err != nil {
	// 	return glob.ErrRet(err.Error())
	// }

	blocks, err := ast.PreprocessAndMakeSourceCodeIntoBlocks(code)
	if err != nil {
		return glob.ErrRet(err.Error())
	}

	p := ast.NewTbParser(curExec.Env.EnvPkgMgr.PkgMgr)
	msgs := []*glob.StmtRet{}
	for _, block := range blocks {
		topStmt, err := p.Stmt(&block)
		if err != nil {
			return glob.ErrRet(err.Error())
		}
		ret := RunStmtInExecutor(curExec, topStmt)
		msgs = append(msgs, ret)
		if ret.IsNotTrue() {
			return glob.NewStmtWithInnerStmtsRet(msgs, ret.Type)
		}
	}
	msgs = append(msgs, curExec.NewTrueStmtRet(importFileStmt))
	msgs = append(msgs, glob.NewStmtTrueWithStmt(exe.SuccessExecStmtStr(importFileStmt)))
	return glob.NewStmtWithInnerStmtsRet(msgs, glob.StmtRetTypeTrue)
}

func RunImportStmtInExecutor(curExec *exe.Executor, importStmt *ast.ImportDirStmt) *glob.StmtRet {
	newPkgImported, newEnvMgr, ret := RunImportStmtToGetEnvMgr(curExec.Env.EnvPkgMgr.PkgMgr, importStmt)
	if ret.IsNotTrue() {
		return ret
	}
	if newPkgImported {
		absPath, err := absPathOfImportStmtPath(curExec.Env.EnvPkgMgr.PkgMgr, importStmt)
		if err != nil {
			return glob.ErrRet(err.Error())
		}
		curExec.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap[absPath] = newEnvMgr
	}

	return curExec.NewTrueStmtRet(importStmt)
}

// return: new imported pkg, new envMgr, globRet
func RunImportStmtToGetEnvMgr(pkgMgr *packageMgr.PkgMgr, importStmt *ast.ImportDirStmt) (bool, *env.EnvMgr, *glob.StmtRet) {
	var importRepoAbsPath string
	var err error

	// 分类：如果 importStmt 是import 全局的包，或者是import其他repo
	if importStmt.IsGlobalPkg {
		importRepoAbsPath, err = glob.GetGlobalPkgAbsPath(importStmt.AsPkgName)
		if err != nil {
			return false, nil, glob.ErrRet(err.Error())
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

			return false, nil, glob.NewStmtTrueWithStmt(fmt.Sprintf("%s\n", importStmt))
		} else {
			// 这个name已经用过了，需要验证一下是不是之前对应的也是目前的abs path
			if path != importRepoAbsPath {
				return false, nil, glob.ErrRet(fmt.Sprintf("error at %s:\npackage name %s is already used for repository %s, it can not be name for %s", importStmt, importStmt.AsPkgName, path, importRepoAbsPath))
			}
		}
	}

	// 把这个包存在 pkgMgr 里
	// 在Run Dir 前存好，因为1. run的时候需要知道现在的 curEnvName 2. 防止循环引用
	pkgMgr.NameAbsPathMap[importStmt.AsPkgName] = importRepoAbsPath
	pkgMgr.AbsPathNamesSetMap[importRepoAbsPath][importStmt.AsPkgName] = struct{}{}
	pkgMgr.AbsPathDefaultNameMap[importRepoAbsPath] = importStmt.AsPkgName

	// 这个repo还没被引用，那么就第一次运行它
	envMgr, retType, rets := RunFileInPkgMgr(filepath.Join(importRepoAbsPath, glob.MainDotLit), importStmt.AsPkgName, pkgMgr, true)
	if retType != glob.StmtRetTypeTrue {
		return false, nil, glob.NewStmtWithInnerStmtsRet(rets, retType)
	}

	return true, envMgr, glob.NewStmtTrueWithStmt(fmt.Sprintf("%s\n", importStmt)).AddInnerStmtRets(rets)
}
