// // Copyright 2024 Jiachen Shen.
// //
// // Licensed under the Apache License, Version 2.0 (the "License");
// // you may not use this file except in compliance with the License.
// // You may obtain a copy of the License at
// //
// //     http://www.apache.org/licenses/LICENSE-2.0
// //
// // Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// // Litex email: <litexlang@outlook.com>
// // Litex website: https://litexlang.com
// // Litex github repository: https://github.com/litexlang/golitex
// // Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_pipeline

// import (
// 	"fmt"
// 	ast "golitex/ast"
// 	env "golitex/environment"
// 	exe "golitex/executor"
// 	glob "golitex/glob"
// 	parser "golitex/parser"
// 	"os"
// 	"path/filepath"
// 	"strings"
// )

// func RunFileWithEnv(path string) glob.GlobRet {
// 	content, err := os.ReadFile(path)
// 	if err != nil {
// 		return glob.NewGlobErr(err.Error()).AddMsg(glob.REPLErrorMessageWithPath(path))
// 	}
// 	return RunSourceCodeWithEnv(string(content), path)
// }

// func RunSourceCodeWithEnv(code string, path string) glob.GlobRet {
// 	curEnv, err := GetEnvWithBuiltinParentEnv()
// 	if err != nil {
// 		return glob.NewGlobErr(err.Error()).AddMsg(glob.REPLErrorMessageWithPath(path))
// 	}
// 	ret := RunSourceCodeInEnv(curEnv, code, path)
// 	return ret
// }

// func RunSourceCodeInEnv(curEnv *env.Env, code string, path string) glob.GlobRet {
// 	stmtSlice, err := parser.ParseSourceCode(code)
// 	if err != nil {
// 		return glob.NewGlobErr(err.Error()).AddMsg(glob.REPLErrorMessageWithPath(path))
// 	}

// 	msgs := []string{}
// 	for _, topStmt := range stmtSlice {
// 		ret := RunStmtAndImportStmtInEnv(curEnv, topStmt)
// 		msgs = append(msgs, ret.String())

// 		if ret.IsNotTrue() {
// 			return glob.NewGlobErr(strings.Join(msgs, "\n")).AddMsg(glob.REPLErrorMessageWithPath(path))
// 		}
// 	}

// 	return glob.NewGlobTrue(strings.Join(msgs, "\n")).AddMsg(glob.REPLMsgWithPath(glob.NewGlobTrue(strings.Join(msgs, "\n")), path))
// }

// func RunStmtAndImportStmtInEnv(curEnv *env.Env, stmt ast.Stmt) glob.GlobRet {
// 	switch asStmt := stmt.(type) {
// 	case *ast.ImportDirStmt:
// 		return RunImportDirStmtInEnv(curEnv, asStmt)
// 	case *ast.ImportFileStmt:
// 		return RunImportFileStmtInEnv(curEnv, asStmt)
// 	default:
// 		executor := exe.NewExecutor(curEnv)
// 		return executor.Stmt(asStmt).ToGlobRet()
// 	}
// }

// // import path as name 的执行：1. 如果之前有过当前包或者引用包里(引用的包也是可见的，然后里面可以给一个path赋予了某个名字)，import path2 as name了，那name同时指向两个包了，那就不行 2. 如果之前没有过，那就可以，然后引入path，如果path已经被引用过了，那就给这个path一个新的名字name 3. path之前还没引用过，那这时候就运行path对应的包。运行方式：新开一个executor，然后运行path对应的包，得到env和pkgMgr, 把 env 和 pkgMgr merge到主executor中。
// func RunImportDirStmtInEnv(curEnv *env.Env, importDirStmt *ast.ImportDirStmt) glob.GlobRet {
// 	// 如果已经存在asPkgName，则直接返回
// 	if path, ok := curEnv.PackageManager.PkgNamePkgPathPairs[importDirStmt.AsPkgName]; ok {
// 		if path != importDirStmt.Path {
// 			return glob.NewGlobErr(fmt.Sprintf("package name %s already exists, and it refers to package %s, not %s", importDirStmt.AsPkgName, path, importDirStmt.Path))
// 		}
// 		return glob.NewGlobTrue(fmt.Sprintf("package %s already imported as %s", importDirStmt.Path, importDirStmt.AsPkgName))
// 	}

// 	// 如果已经在curEnv.PackageManager.PkgPathEnvPairs中，则直接返回
// 	if _, ok := curEnv.PackageManager.PkgPathEnvPairs[importDirStmt.Path]; ok {
// 		curEnv.PackageManager.PkgNamePkgPathPairs[importDirStmt.AsPkgName] = importDirStmt.Path
// 		return glob.NewGlobTrue(fmt.Sprintf("package %s already imported. Now it has another name: %s", importDirStmt.Path, importDirStmt.AsPkgName))
// 	}

// 	// Resolve package path: if not absolute, resolve from system root directory (~/litexlang)
// 	resolvedPath, err := glob.ResolvePackagePath(importDirStmt.Path)
// 	if err != nil {
// 		return glob.NewGlobErr(err.Error())
// 	}
// 	mainFileContent, err := os.ReadFile(filepath.Join(resolvedPath, glob.MainDotLit))
// 	if err != nil {
// 		return glob.NewGlobErr(err.Error())
// 	}

// 	builtinEnv, err := GetEnvWithBuiltinParentEnv()
// 	if err != nil {
// 		return glob.NewGlobErr(err.Error())
// 	}
// 	ret := RunSourceCodeInEnv(builtinEnv, string(mainFileContent), resolvedPath)
// 	if ret.IsNotTrue() {
// 		return ret
// 	}

// 	err = curEnv.PackageManager.MergeGivenExecPkgMgr(importDirStmt, builtinEnv)
// 	if err != nil {
// 		return glob.NewGlobErr(err.Error())
// 	}
// 	return glob.NewGlobTrue(fmt.Sprintf("imported package %s as %s", importDirStmt.Path, importDirStmt.AsPkgName))
// }

// // expandTilde expands ~ to the user's home directory.
// // Note: ~ is primarily used on Unix/Linux/macOS. Windows users typically
// // use %USERPROFILE% or full paths like C:\Users\username\...
// func expandTildeWithEnv(path string) (string, error) {
// 	// Handle ~/path format
// 	if strings.HasPrefix(path, "~/") {
// 		homeDir, err := os.UserHomeDir()
// 		if err != nil {
// 			return "", fmt.Errorf("failed to get home directory: %w", err)
// 		}
// 		// Use filepath.Join to handle cross-platform path separators
// 		restOfPath := path[2:]
// 		return filepath.Join(homeDir, restOfPath), nil
// 	}

// 	// Handle just ~
// 	if path == "~" {
// 		return os.UserHomeDir()
// 	}

// 	// No expansion needed
// 	return path, nil
// }

// func RunImportFileStmtInEnv(curEnv *env.Env, importFileStmt *ast.ImportFileStmt) glob.GlobRet {
// 	// Expand ~ to home directory if present
// 	expandedPath, err := expandTildeWithEnv(importFileStmt.Path)
// 	if err != nil {
// 		return glob.NewGlobErr(fmt.Sprintf("failed to expand path: %s", err.Error()))
// 	}

// 	content, err := os.ReadFile(expandedPath)
// 	if err != nil {
// 		return glob.NewGlobErr(err.Error())
// 	}
// 	return RunSourceCodeInEnv(curEnv, string(content), importFileStmt.Path)
// }
