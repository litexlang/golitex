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
	env "golitex/environment"
	exe "golitex/executor"
	glob "golitex/glob"
	parser "golitex/parser"
	"io"
	"os"
	"strconv"
	"strings"
	"time"
)

func RunSourceCode(curEnv *env.Env, code string) (string, glob.SysSignal, *env.Env, error) {
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		return "", glob.SysSignalParseError, nil, err
	}

	var executor *exe.Executor

	if curEnv == nil {
		executor, err = InitPipelineExecutor()
		curEnv = executor.GetBuiltinEnv()
	} else {
		executor = exe.NewExecutor(curEnv)
	}

	if err != nil {
		return "", glob.SysSignalRuntimeError, nil, err
	}

	msgOfTopStatements := []string{}

	// maintain a dict of paths that have been imported
	pkgMgr := NewPackageManager()
	_ = pkgMgr

	for _, topStmt := range topStmtSlice {
		var execRet exe.ExecRet = exe.NewExecErr("")
		var msg string
		var err error

		switch topStmt.(type) {
		case *ast.ImportDirStmt:
			msg, signal, err := pkgMgr.NewPkg(curEnv, topStmt.(*ast.ImportDirStmt).Path)
			if err != nil || signal != glob.SysSignalTrue {
				return msg, signal, nil, err
			}
		case *ast.ImportFileStmt:
			msg, signal, err := RunImportFileStmt(executor.Env, topStmt.(*ast.ImportFileStmt))

			msgOfTopStatements = append(msgOfTopStatements, executor.GetMsgAsStr0ToEnd())
			msgOfTopStatements = append(msgOfTopStatements, msg)

			if err != nil || signal != glob.SysSignalTrue {
				msgOfTopStatements = append(msgOfTopStatements, fmt.Sprintf("import file error: %s", topStmt.String()))
				return strings.TrimSpace(strings.Join(msgOfTopStatements, "\n")), glob.SysSignalRuntimeError, nil, err
			}
		default:
			execRet = executor.Stmt(topStmt)

			msgOfTopStatements = append(msgOfTopStatements, executor.GetMsgAsStr0ToEnd())
			msgOfTopStatements = append(msgOfTopStatements, msg)

			if execRet.IsErr() {
				return strings.TrimSpace(strings.Join(msgOfTopStatements, "\n")), glob.SysSignalRuntimeError, nil, err
			}
			if execRet.IsUnknown() {
				return strings.TrimSpace(strings.Join(msgOfTopStatements, "\n")), glob.SysSignalRuntimeError, nil, fmt.Errorf("execution failed, line %d", topStmt.GetLine())
			}
		}
	}

	secondUpMostEnv := executor.GetSecondUpMostEnv()

	return strings.TrimSpace(strings.Join(msgOfTopStatements, "\n")), glob.SysSignalTrue, secondUpMostEnv, nil
}

func RunImportFileStmt(curEnv *env.Env, importFileStmt *ast.ImportFileStmt) (string, glob.SysSignal, error) {
	content, err := os.ReadFile(importFileStmt.Path)
	if err != nil {
		return fmt.Sprintf("failed to read file %s: %s", importFileStmt.Path, err.Error()), glob.SysSignalSystemError, err
	}
	msg, signal, _, err := RunSourceCode(curEnv, string(content))
	return msg, signal, err
}

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

		currentLineStr = glob.RemoveWindowsCarriageReturn(currentLineStr)
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
	switch topStmt.(type) {
	case *ast.ImportDirStmt:
		return glob.NewGlobTrue("")
	case *ast.ImportFileStmt:
		return glob.NewGlobTrue("")
	default:
		execRet := curExec.Stmt(topStmt)
		if execRet.IsNotTrue() {
			return execRet.ToGlobRet()
		}
		return glob.NewGlobTrue("")
	}
}
