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

func RunCodeInPkgMgr(code string, pkgMgr *packageMgr.PkgMgr, removeBuiltinEnv bool) (*env.EnvMgr, string, []ast.StmtRet) {
	envPkgMgr := env.NewEnvPkgMgr(pkgMgr)
	envMgr, err := NewBuiltinEnvMgrWithNewEmptyEnv(envPkgMgr)
	if err != nil {
		return nil, glob.ERROR, []ast.StmtRet{ast.StmtErrRet(nil, err.Error())}
	}

	blocks, err := ast.PreprocessAndMakeSourceCodeIntoBlocks(code)
	if err != nil {
		return nil, glob.ERROR, []ast.StmtRet{ast.StmtErrRet(nil, err.Error())}
	}

	p := ast.NewTbParser(pkgMgr)
	curExec := exe.NewExecutor(envMgr)
	innerGlobRets := []ast.StmtRet{}
	for _, block := range blocks {
		topStmt, err := p.Stmt(&block)
		if err != nil {
			return nil, glob.ERROR, []ast.StmtRet{ast.StmtErrRet(nil, err.Error())}
		}
		ret := RunStmtInExecutor(curExec, topStmt)

		if ret.IsNotTrue() {
			if ret.IsErr() {
				return nil, glob.ERROR, []ast.StmtRet{ret}
			}
			return nil, glob.UNKNOWN, []ast.StmtRet{ret}
		} else {
			innerGlobRets = append(innerGlobRets, ret)
		}
	}

	if removeBuiltinEnv {
		return envMgr, glob.TRUE, innerGlobRets
	}

	return envMgr, glob.TRUE, innerGlobRets
}

func RunFileInPkgMgr(fileAbsPath string, curPkgName string, pkgMgr *packageMgr.PkgMgr, removeBuiltinEnv bool) (*env.EnvMgr, string, []ast.StmtRet) {
	if fileAbsPath == "" {
		return nil, glob.ERROR, []ast.StmtRet{ast.StmtErrRet(nil, "filePath is empty")}
	}

	cleanFileAbsPath := filepath.Clean(fileAbsPath)
	if cleanFileAbsPath == "" {
		return nil, glob.ERROR, []ast.StmtRet{ast.StmtErrRet(nil, fmt.Sprintf("file path %s error", fileAbsPath))}
	}

	// 更新 current working repo
	previousCurRepoAbsPath := pkgMgr.CurRepoAbsPath
	previousCurPkgDefaultName := pkgMgr.CurPkgDefaultName
	pkgMgr.CurRepoAbsPath = filepath.Dir(cleanFileAbsPath)
	pkgMgr.CurPkgDefaultName = curPkgName

	defer func() {
		pkgMgr.CurRepoAbsPath = previousCurRepoAbsPath
		pkgMgr.CurPkgDefaultName = previousCurPkgDefaultName
	}()

	// 获得那个 main.lit
	code, err := os.ReadFile(cleanFileAbsPath)
	if err != nil {
		return nil, glob.ERROR, []ast.StmtRet{ast.StmtErrRet(nil, err.Error())}
	}

	return RunCodeInPkgMgr(string(code), pkgMgr, removeBuiltinEnv)
}
