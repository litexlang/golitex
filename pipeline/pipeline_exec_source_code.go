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
	exe "golitex/executor"
	glob "golitex/glob"
	parser "golitex/parser"
	"io"
	"os"
	"strconv"
	"strings"
	"time"
)

// main function for running a single code and return the message
func ExecuteCodeAndReturnMessage(code string) (string, glob.SysSignal, error) {
	msgOfTopStatements, signal, err := executeCodeAndReturnMessageSlice(code)
	if err != nil {
		msgOfTopStatements = append(msgOfTopStatements, err.Error())
	}
	ret := strings.TrimSpace(strings.Join(msgOfTopStatements, "\n"))
	return ret, signal, err
}

func executeCodeAndReturnMessageSlice(code string) ([]string, glob.SysSignal, error) {
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		return nil, glob.SysSignalParseError, err
	}

	executor, err := pipelineExecutorInit()
	if err != nil {
		return nil, glob.SysSignalRuntimeError, err
	}

	msgOfTopStatements := []string{}

	for _, topStmt := range topStmtSlice {
		execState, msg, err := executor.Stmt(topStmt)
		msgOfTopStatements = append(msgOfTopStatements, executor.GetMsgAsStr0ToEnd())
		msgOfTopStatements = append(msgOfTopStatements, msg)
		if err != nil {
			return msgOfTopStatements, glob.SysSignalRuntimeError, err
		}
		if execState != glob.ExecStateTrue {
			return msgOfTopStatements, glob.SysSignalRuntimeError, fmt.Errorf("execution failed, line %d", topStmt.GetLine())
		}
	}

	return msgOfTopStatements, glob.SysSignalTrue, nil
}

func ExecuteCodeAndReturnMessageSliceGivenSettings(code string, executor *exe.Executor) ([]string, glob.SysSignal, error) {
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		return nil, glob.SysSignalParseError, err
	}

	msgOfTopStatements := []string{}

	for _, topStmt := range topStmtSlice {
		execState, _, err := executor.Stmt(topStmt)
		if err != nil {
			return nil, glob.SysSignalRuntimeError, err
		}

		msgOfTopStatements = append(msgOfTopStatements, executor.GetMsgAsStr0ToEnd())

		if execState != glob.ExecStateTrue {
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
			m = strings.TrimRight(m, " \r\t\n")
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

func RunREPLInTerminal() {
	executor, err := pipelineExecutorInit()
	if err != nil {
		fmt.Println("Error initializing pipeline:", err)
		return
	}

	reader := bufio.NewReader(os.Stdin)
	writer := os.Stdout

	year := time.Now().Year()

	fmt.Fprintln(writer, fmt.Sprintf("Litex %s Copyright (C) 2024-%s litexlang.com ", glob.VERSION, strconv.Itoa(year)))

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

		// Normalize line endings for cross-platform compatibility (Windows \r\n -> \n)
		currentLineStr = strings.ReplaceAll(currentLineStr, "\r", "")
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
