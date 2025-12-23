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

func RunCodeInPkgMgr(code string, pkgMgr *packageMgr.PkgMgr, removeBuiltinEnv bool) (*env.EnvMgr, glob.GlobRet) {
	envPkgMgr := env.NewEnvPkgMgr(pkgMgr)
	envMgr, err := NewBuiltinEnvMgr(envPkgMgr)
	if err != nil {
		return nil, glob.NewGlobErr(err.Error())
	}

	stmtSlice, err := ast.ParseSourceCode(code, pkgMgr)
	if err != nil {
		return nil, glob.NewGlobErr(err.Error())
	}

	curExec := exe.NewExecutor(envMgr)

	msgs := []string{}
	for _, topStmt := range stmtSlice {
		ret := RunStmtInExecutor(curExec, topStmt)
		msgs = append(msgs, ret.String())

		if ret.IsNotTrue() {
			return nil, glob.NewGlobErr(strings.Join(msgs, "\n"))
		}
	}

	if removeBuiltinEnv {
		envMgrWithoutBuiltinLogic := envMgr.RemoveBuiltinEnv()
		return envMgrWithoutBuiltinLogic, glob.NewGlobTrue(strings.Join(msgs, "\n"))
	}

	return envMgr, glob.NewGlobTrue(strings.Join(msgs, "\n"))
}

func RunFileInPkgMgr(fileAbsPath string, curPkgName string, pkgMgr *packageMgr.PkgMgr, removeBuiltinEnv bool) (*env.EnvMgr, glob.GlobRet) {
	if fileAbsPath == "" {
		return nil, glob.NewGlobErr("filePath is empty")
	}

	cleanFileAbsPath := filepath.Clean(fileAbsPath)
	if cleanFileAbsPath == "" {
		return nil, glob.NewGlobErr(fmt.Sprintf("file path %s error", fileAbsPath))
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
		return nil, glob.NewGlobErr(err.Error())
	}

	return RunCodeInPkgMgr(string(code), pkgMgr, removeBuiltinEnv)
}
