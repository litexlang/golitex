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
	exe "golitex/executor"
	glob "golitex/glob"
	parser "golitex/parser"
	"os"
	"path/filepath"
)

func RunFile(path string) glob.GlobRet {
	content, err := os.ReadFile(path)
	if err != nil {
		return glob.NewGlobErr(err.Error())
	}
	return RunSourceCode(string(content))
}

func RunSourceCode(code string) glob.GlobRet {
	executor, err := InitPipelineExecutor()
	if err != nil {
		return glob.NewGlobErr(err.Error())
	}
	return RunSourceCodeInExecutor(executor, code)
}

func RunSourceCodeInExecutor(curExec *exe.Executor, code string) glob.GlobRet {
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		return glob.NewGlobErr(err.Error())
	}

	msgOfTopStatements := []string{}

	for _, topStmt := range topStmtSlice {
		ret := RunTopStmtInPipeline(curExec, topStmt)
		msgOfTopStatements = append(msgOfTopStatements, curExec.GetMsgAsStr0ToEnd())
		msgOfTopStatements = append(msgOfTopStatements, ret.GetMsgs()...)

		if ret.IsNotTrue() {
			// 将消息添加到 globRet 中
			if ret.IsErr() {
				return glob.NewGlobErrWithMsgs(msgOfTopStatements)
			}
			// IsUnknown
			allMsgs := append(msgOfTopStatements, "execution failed: unknown factual statement\n")
			return glob.NewGlobErrWithMsgs(allMsgs)
		}
	}

	return glob.NewGlobTrueWithMsgs(msgOfTopStatements)
}

func RunTopStmtInPipeline(curExec *exe.Executor, topStmt ast.Stmt) glob.GlobRet {
	switch topStmt := topStmt.(type) {
	case *ast.ImportDirStmt:
		return RunImportDirStmtInExec(curExec, topStmt)
	case *ast.ImportFileStmt:
		return RunImportFileStmtInExec(curExec, topStmt)
	default:
		return curExec.Stmt(topStmt).ToGlobRet()
	}
}

// import path as name 的执行：1. 如果之前有过当前包或者引用包里(引用的包也是可见的，然后里面可以给一个path赋予了某个名字)，import path2 as name了，那name同时指向两个包了，那就不行 2. 如果之前没有过，那就可以，然后引入path，如果path已经被引用过了，那就给这个path一个新的名字name 3. path之前还没引用过，那这时候就运行path对应的包。运行方式：新开一个executor，然后运行path对应的包，得到env和pkgMgr, 把 env 和 pkgMgr merge到主executor中。
func RunImportDirStmtInExec(curExec *exe.Executor, importDirStmt *ast.ImportDirStmt) glob.GlobRet {
	// 如果已经存在asPkgName，则直接返回
	if path, ok := curExec.PkgMgr.PkgNamePkgPathPairs[importDirStmt.AsPkgName]; ok {
		if path != importDirStmt.Path {
			return glob.NewGlobErr(fmt.Sprintf("package name %s already exists, and it refers to package %s, not %s", importDirStmt.AsPkgName, path, importDirStmt.Path))
		}
		return glob.NewGlobTrue(fmt.Sprintf("package %s already imported as %s", importDirStmt.Path, importDirStmt.AsPkgName))
	}

	// 如果已经在curExec.PkgMgr.PkgEnvPairs中，则直接返回
	if _, ok := curExec.PkgMgr.PkgPathEnvPairs[importDirStmt.Path]; ok {
		curExec.PkgMgr.PkgNamePkgPathPairs[importDirStmt.AsPkgName] = importDirStmt.Path
		return glob.NewGlobTrue(fmt.Sprintf("package %s already imported. Now it has another name: %s", importDirStmt.Path, importDirStmt.AsPkgName))
	}

	mainFileContent, err := os.ReadFile(filepath.Join(importDirStmt.Path, glob.MainDotLit))
	if err != nil {
		return glob.NewGlobErr(err.Error())
	}

	builtinEnv := GetBuiltinEnv()
	executorToRunDir := exe.NewExecutor(builtinEnv, exe.NewPackageManager())
	ret := RunSourceCodeInExecutor(executorToRunDir, string(mainFileContent))
	if ret.IsNotTrue() {
		return ret
	}

	err = curExec.PkgMgr.MergeGivenExecPkgMgr(importDirStmt, executorToRunDir)
	if err != nil {
		return glob.NewGlobErr(err.Error())
	}
	return glob.NewGlobTrue(fmt.Sprintf("imported package %s as %s", importDirStmt.Path, importDirStmt.AsPkgName))
}

func RunImportFileStmtInExec(curExec *exe.Executor, importFileStmt *ast.ImportFileStmt) glob.GlobRet {
	content, err := os.ReadFile(importFileStmt.Path)
	if err != nil {
		return glob.NewGlobErr(err.Error())
	}
	return RunSourceCodeInExecutor(curExec, string(content))
}
