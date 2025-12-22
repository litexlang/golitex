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
	"os"
	"path/filepath"
	"strings"
)

func RunFile(path string) glob.GlobRet {
	content, err := os.ReadFile(path)
	if err != nil {
		return glob.NewGlobErr(err.Error()).AddMsg(glob.REPLErrorMessageWithPath(path))
	}
	return RunSourceCode(string(content), path)
}

func RunSourceCode(code string, path string) glob.GlobRet {
	// 获得 path所在的 repo
	repoPath, err := filepath.Abs(filepath.Dir(path))
	if err != nil {
		return glob.NewGlobErr(err.Error()).AddMsg(glob.REPLErrorMessageWithPath(path))
	}
	envPkgMgr := env.NewPkgMgr(repoPath)
	envMgr, err := GetBuiltinEnvMgr(envPkgMgr)
	if err != nil {
		return glob.NewGlobErr(err.Error()).AddMsg(glob.REPLErrorMessageWithPath(path))
	}
	executor := exe.NewExecutor(envMgr.NewEnv())
	ret := RunSourceCodeInExecutor(executor, code, path)
	return ret
}

func RunSourceCodeInExecutor(curExec *exe.Executor, code string, path string) glob.GlobRet {
	// TODO: 现在问题很大，只能在parse的时候默认现在是""，所以不能parse的时候就让对应的参数变成其他的包名.xxx
	stmtSlice, err := ast.ParseSourceCode(code, "", curExec.Env.PkgMgr.AbsPathNameMgr)
	if err != nil {
		return glob.NewGlobErr(err.Error()).AddMsg(glob.REPLErrorMessageWithPath(path))
	}

	msgs := []string{}
	for _, topStmt := range stmtSlice {
		ret := RunStmtAndImportStmtInExecutor(curExec, topStmt)
		msgs = append(msgs, ret.String())

		if ret.IsNotTrue() {
			return glob.NewGlobErr(strings.Join(msgs, "\n")).AddMsg(glob.REPLErrorMessageWithPath(path))
		}
	}

	return glob.NewGlobTrue(strings.Join(msgs, "\n")).AddMsg(glob.REPLMsgWithPath(glob.NewGlobTrue(strings.Join(msgs, "\n")), path))
}

func RunStmtAndImportStmtInExecutor(curExec *exe.Executor, stmt ast.Stmt) glob.GlobRet {
	switch asStmt := stmt.(type) {
	case *ast.ImportDirStmt:
		return RunImportDirStmtInExec(curExec, asStmt)
	case *ast.RunFileStmt:
		return RunFileStmtInExec(curExec, asStmt)
	default:
		return curExec.Stmt(asStmt).ToGlobRet()
	}
}

// import path as name 的执行：1. 如果之前有过当前包或者引用包里(引用的包也是可见的，然后里面可以给一个path赋予了某个名字)，import path2 as name了，那name同时指向两个包了，那就不行 2. 如果之前没有过，那就可以，然后引入path，如果path已经被引用过了，那就给这个path一个新的名字name 3. path之前还没引用过，那这时候就运行path对应的包。运行方式：新开一个executor，然后运行path对应的包，得到env和pkgMgr, 把 env 和 pkgMgr merge到主executor中。
func RunImportDirStmtInExec(curExec *exe.Executor, importDirStmt *ast.ImportDirStmt) glob.GlobRet {
	var importRelativePath string = ""
	var err error = nil

	if importDirStmt.IsGlobalPkg {
		importRelativePath = importDirStmt.RelativePathOrGlobalPkgName
	} else {
		importRelativePath, err = GetRelativePathFromGlobalPkgToWorkingRepo(curExec, importDirStmt.RelativePathOrGlobalPkgName)
		if err != nil {
			return glob.NewGlobErr(err.Error())
		}
	}

	importAbsRepoPath := filepath.Join(curExec.Env.PkgMgr.CurAbsRepoPath, importRelativePath)

	// 如果已经存在asPkgName，则直接返回
	if path, ok := curExec.Env.PkgMgr.AbsPathNameMgr.NameAbsPathMap[importDirStmt.AsPkgName]; ok {
		if path != importAbsRepoPath {
			return glob.NewGlobErr(fmt.Sprintf("package name %s already exists, and it refers to package %s, not %s", importDirStmt.AsPkgName, path, importAbsRepoPath))
		}
		return glob.NewGlobTrue(fmt.Sprintf("package %s already imported as %s", importAbsRepoPath, importDirStmt.AsPkgName))
	}

	// 如果已经在curExec.PkgMgr.PkgEnvPairs中，则直接返回
	if _, ok := curExec.Env.PkgMgr.AbsPkgPathEnvPairs[importAbsRepoPath]; ok {
		if err := curExec.Env.PkgMgr.AbsPathNameMgr.AddNamePath(importDirStmt.AsPkgName, importAbsRepoPath); err != nil {
			return glob.NewGlobErr(err.Error())
		}
		return glob.NewGlobTrue(fmt.Sprintf("package %s already imported. Now it has another name: %s", importAbsRepoPath, importDirStmt.AsPkgName))
	}

	// Resolve package path: if not absolute, resolve from system root directory (~/litexlang)
	absoluteMainFilePath := filepath.Join(importAbsRepoPath, glob.MainDotLit)

	// 把 entrance path 改成 absRepoPath
	previousEntranceRepoPath := curExec.Env.PkgMgr.CurAbsRepoPath
	curExec.Env.PkgMgr.CurAbsRepoPath = importAbsRepoPath
	defer func() {
		curExec.Env.PkgMgr.CurAbsRepoPath = previousEntranceRepoPath
	}()

	if _, ok := curExec.Env.PkgMgr.AbsPathNameMgr.NameAbsPathMap[importDirStmt.AsPkgName]; ok {
		return glob.NewGlobErr(fmt.Sprintf("package name %s is used as package name for package %s. It cannot be used as package name for another package %s", importDirStmt.AsPkgName, importAbsRepoPath, curExec.Env.PkgMgr.AbsPathNameMgr.NameAbsPathMap[importDirStmt.AsPkgName]))
	}

	mainFileContent, err := os.ReadFile(absoluteMainFilePath)
	if err != nil {
		return glob.NewGlobErr(err.Error())
	}

	// envPkgMgr := env.NewPkgMgr(importAbsRepoPath)
	envPkgMgr := curExec.Env.PkgMgr // REMARK 直接把现在的pkgMgr传进去，因为已经把entrance repo path改成importAbsRepoPath了
	builtinEnvMgr, err := GetBuiltinEnvMgr(envPkgMgr)
	if err != nil {
		return glob.NewGlobErr(err.Error())
	}

	executorToRunDir := exe.NewExecutor(builtinEnvMgr.NewEnv())
	ret := RunSourceCodeInExecutor(executorToRunDir, string(mainFileContent), importRelativePath)
	if ret.IsNotTrue() {
		return ret
	}

	err = curExec.Env.PkgMgr.MergeGivenExecPkgMgr(importAbsRepoPath, importDirStmt.AsPkgName, executorToRunDir.Env)
	if err != nil {
		return glob.NewGlobErr(err.Error())
	}
	return glob.NewGlobTrue(fmt.Sprintf("imported package %s as %s", importRelativePath, importDirStmt.AsPkgName))
}

func RunFileStmtInExec(curExec *exe.Executor, importFileStmt *ast.RunFileStmt) glob.GlobRet {
	// 把 entrance repo path 和 importFileStmt.Path结合起来
	path := filepath.Join(curExec.Env.PkgMgr.CurAbsRepoPath, importFileStmt.Path)

	content, err := os.ReadFile(path)
	if err != nil {
		return glob.NewGlobErr(err.Error())
	}

	return RunSourceCodeInExecutor(curExec, string(content), path)
}

// GetRelativePathFromGlobalPkgToWorkingRepo 获取全局包路径和当前执行器工作环境的相对路径
// 返回从 globalPkg 到 curExec 的 working env 的相对路径
func GetRelativePathFromGlobalPkgToWorkingRepo(curExec *exe.Executor, globalPkgName string) (string, error) {
	globalPkgPath, err := glob.GetGlobalPkgAbsPath(globalPkgName)
	if err != nil {
		return "", err
	}

	workingEnvPath := curExec.Env.PkgMgr.CurAbsRepoPath

	relPath, err := filepath.Rel(globalPkgPath, workingEnvPath)
	if err != nil {
		return "", fmt.Errorf("failed to calculate relative path from %s to %s: %w", globalPkgPath, workingEnvPath, err)
	}

	return relPath, nil
}
