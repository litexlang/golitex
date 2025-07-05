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
// Litex website: https://litexlang.org
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
	"strings"
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

	// curEnv := env.NewEnv(nil, nil)
	// executor := exe.NewExecutorWithInit(curEnv)
	// curEnv.Init()
	// executor := *exe.NewExecutor(curEnv)

	msgOfTopStatements := []string{}

	for _, topStmt := range topStmtSlice {
		execState, err := executor.Stmt(topStmt)
		msgOfTopStatements = append(msgOfTopStatements, executor.GetMsgAsStr0ToEnd())
		if err != nil {
			return msgOfTopStatements, glob.SysSignalRuntimeError, err
		}
		if execState != glob.ExecState_True {
			return msgOfTopStatements, glob.SysSignalRuntimeError, fmt.Errorf("execution failed")
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
		execState, err := executor.Stmt(topStmt)
		if err != nil {
			return nil, glob.SysSignalRuntimeError, err
		}
		if execState != glob.ExecState_True {
			return nil, glob.SysSignalRuntimeError, fmt.Errorf("execution failed")
		}
		msgOfTopStatements = append(msgOfTopStatements, executor.GetMsgAsStr0ToEnd())
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
		fmt.Fprintln(writer, builder.String()[:len(builder.String())-1])
	}
}

func RunREPLInTerminal() {
	executor, err := pipelineExecutorInit()
	if err != nil {
		fmt.Println("Error initializing pipeline:", err)
		return
	}

	// curEnv := env.NewEnv(nil, nil)
	// executor := exe.NewExecutorWithInit(curEnv)
	// curEnv.Init()
	// executor := exe.NewExecutor(curEnv)

	reader := bufio.NewReader(os.Stdin)
	writer := os.Stdout

	fmt.Println("Litex-beta - Type your code or 'exit' to quit\nWarning: not yet ready for production use.")

	for {
		code, err := listenOneStatement(reader, writer)
		if err != nil {
			fmt.Fprintf(writer, "[Error] %v\n", err)
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

func listenOneStatement(reader *bufio.Reader, writer io.Writer) (string, error) {
	var input strings.Builder
	fmt.Fprint(writer, ">>> ")
	currentScopeDepth := 0

	for {
		if currentScopeDepth > 0 {
			fmt.Fprint(writer, "... ") // 末尾的+4是未来和">>> "对齐
			input.WriteString("    ")

			currentLineStr, err := reader.ReadString('\n')
			trimmedLine := strings.TrimRight(currentLineStr, " \t\n\r")

			if trimmedLine == "" {
				break
			}

			if err != nil {
				return "", fmt.Errorf("error reading input: %v", err)
			}
			input.WriteString(currentLineStr)

		} else {
			currentLineStr, err := reader.ReadString('\n')
			if err != nil {
				return "", fmt.Errorf("error reading input: %v", err)
			}
			input.WriteString(currentLineStr)

			// input 的非空白的最后一位 不是 :
			trimmedLine := strings.TrimRight(currentLineStr, " \t\n\r")
			if trimmedLine == "" || !strings.HasSuffix(trimmedLine, ":") {
				break
			} else {
				currentScopeDepth = 1

			}
		}
	}
	return input.String(), nil
}
