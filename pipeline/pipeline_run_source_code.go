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
	"bufio"
	"fmt"
	ast "golitex/ast"
	exe "golitex/executor"
	glob "golitex/glob"
	parser "golitex/parser"
	"io"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"time"
)

func ExecuteCodeAndReturnMessageSliceGivenSettings(code string, executor *exe.Executor) ([]string, glob.SysSignal, error) {
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		return nil, glob.SysSignalParseError, err
	}

	msgOfTopStatements := []string{}

	for _, topStmt := range topStmtSlice {
		execState := executor.Stmt(topStmt)
		if execState.IsErr() {
			return nil, glob.SysSignalRuntimeError, fmt.Errorf(execState.String())
		}

		msgOfTopStatements = append(msgOfTopStatements, executor.GetMsgAsStr0ToEnd())

		if execState.IsUnknown() || execState.IsErr() {
			return msgOfTopStatements, glob.SysSignalRuntimeError, fmt.Errorf("execution failed")
		}
	}

	return msgOfTopStatements, glob.SysSignalTrue, nil
}

func printMessagesToWriter(writer io.Writer, msg []string) {
	if len(msg) > 0 {
		// fmt.Printf("\n")
		// 如果有连续两行是空白的换行那不允许多个空行出现
		isConsecutiveEmptyLine := true
		var builder strings.Builder

		for _, m := range msg {
			// 让m的最后一位是换行符
			m = strings.TrimRight(m, " \t\n")
			if strings.TrimSpace(m) == "" {
				if isConsecutiveEmptyLine {
					continue
				}
				isConsecutiveEmptyLine = true
			} else {
				isConsecutiveEmptyLine = false
				builder.WriteString(m)
			}
			builder.WriteString("\n")
		}

		result := builder.String()
		if len(result) > 0 {
			// Remove the trailing newline
			fmt.Fprintln(writer, result[:len(result)-1])
		}
	}
}

const helpMessage = `help: show this help message
exit: exit the REPL
clear: refresh the whole environment
`

func RunREPLInTerminal(version string) {
	executor, err := InitPipelineExecutor()
	if err != nil {
		fmt.Println("Error initializing pipeline:", err)
		return
	}

	reader := bufio.NewReader(os.Stdin)
	writer := os.Stdout

	year := time.Now().Year()

	fmt.Fprintf(writer, "Litex %s Copyright (C) 2024-%s litexlang.com Type 'help' for help\nNOT READY FOR PRODUCTION USE\n", version, strconv.Itoa(year))

	for {
		code, err := listenOneStatementFromTerminal(reader, writer)
		if err != nil {
			fmt.Fprintf(writer, "[Error] %s\n", err)
			continue
		}

		// Have to trim space because there is \n at the end of code
		if strings.TrimSpace(code) == "exit" {
			fmt.Fprintf(writer, glob.REPLGoodbyeMessage)
			return
		}

		if strings.TrimSpace(code) == "help" {
			fmt.Fprintf(writer, helpMessage)
			continue
		}

		msg, signal, err := ExecuteCodeAndReturnMessageSliceGivenSettings(code, executor)
		if err != nil || signal != glob.SysSignalTrue {
			printMessagesToWriter(writer, msg)
			fmt.Fprintf(writer, glob.REPLFailedMessage)
			continue
		}

		printMessagesToWriter(writer, msg)
		fmt.Fprintf(writer, glob.REPLSuccessMessage)
	}
}

func listenOneStatementFromTerminal(reader *bufio.Reader, writer io.Writer) (string, error) {
	var input strings.Builder
	fmt.Fprint(writer, ">>> ")
	currentScopeDepth := 0

	for {
		currentLineStr, err := reader.ReadString('\n')
		if err != nil {
			return "", fmt.Errorf("error reading input: %s", err)
		}

		currentLineStr = glob.RemoveWindowsCarriage(currentLineStr)
		trimmedLine := strings.TrimRight(currentLineStr, " \t\n")

		if currentScopeDepth > 0 {
			if trimmedLine == "" {
				break
			}

			input.WriteString("    ")
			input.WriteString(currentLineStr)

			fmt.Fprint(writer, "... ") // 为下一行准备提示符

		} else {
			input.WriteString(currentLineStr)

			// input 的非空白的最后一位 不是 :
			if trimmedLine == "" || !strings.HasSuffix(trimmedLine, ":") {
				break
			} else {
				currentScopeDepth = 1
				fmt.Fprint(writer, "... ") // 为下一行准备提示符
			}
		}
	}
	return input.String(), nil
}

func RunSourceCodeInExecutor(curExec *exe.Executor, code string) glob.GlobRet {
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		return glob.NewGlobErr(err.Error())
	}

	for _, topStmt := range topStmtSlice {
		ret := RunTopStmtInPipeline(curExec, topStmt)
		if ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewGlobTrue("")
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

	mainFileContent, err := os.ReadFile(filepath.Join(importDirStmt.Path, glob.PkgEntranceFileNameMainDotLit))
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

func RunSourceCode(code string) glob.GlobRet {
	executor, err := InitPipelineExecutor()
	if err != nil {
		return glob.NewGlobErr(err.Error())
	}
	return RunSourceCodeInExecutor(executor, code)
}

func RunFile(path string) glob.GlobRet {
	content, err := os.ReadFile(path)
	if err != nil {
		return glob.NewGlobErr(err.Error())
	}
	return RunSourceCode(string(content))
}
