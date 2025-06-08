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
// Litex discord server: https://discord.gg/uvrHM7eS

package litex_pipeline

import (
	"bufio"
	"fmt"
	env "golitex/environment"
	exe "golitex/exe"
	glob "golitex/glob"
	parser "golitex/parser"
	"io"
	"os"
	"strings"
)

func ExecuteCodeAndReturnMessage(code string) (string, glob.SysSignal, error) {
	msgOfTopStatements, signal, err := executeCodeAndReturnMessageSlice(code)
	if err != nil {
		return "", signal, err
	}
	ret := strings.Join(msgOfTopStatements, "\n\n\n")
	return ret, signal, nil
}

func executeCodeAndReturnMessageSlice(code string) ([]string, glob.SysSignal, error) {
	topStmtSlice, err := parser.ParseSourceCode(code, parser.NewParserEnv())
	if err != nil {
		return nil, glob.SysSignalParseError, err
	}
	curEnv := env.NewEnv(nil, nil)
	executor := *exe.NewExecutor(curEnv)

	msgOfTopStatements := []string{}

	for _, topStmt := range topStmtSlice {
		execState, err := executor.TopLevelStmt(&topStmt)
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

func ExecuteCodeAndReturnMessageSliceGivenSettings(code string, parserEnv *parser.ParserEnv, executor *exe.Executor) ([]string, glob.SysSignal, error) {
	topStmtSlice, err := parser.ParseSourceCode(code, parserEnv)
	if err != nil {
		return nil, glob.SysSignalParseError, err
	}

	msgOfTopStatements := []string{}

	for _, topStmt := range topStmtSlice {
		execState, err := executor.TopLevelStmt(&topStmt)
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

// listen processes input from a reader and writes output to a writer
func listen(reader *bufio.Reader, writer io.Writer, parserEnv *parser.ParserEnv, executor *exe.Executor) error {
	for {
		fmt.Fprint(writer, ">>> ")
		var input strings.Builder
		currentScopeDepth := 0

		for {
			if currentScopeDepth > 0 {
				fmt.Fprint(writer, "... ") // 末尾的+4是未来和">>> "对齐
				input.WriteString("    ")

				currentLineStr, err := reader.ReadString('\n')
				trimmedLine := strings.TrimRight(currentLineStr, " \t\n\r")

				if trimmedLine == "" {
					goto ProcessStatement
				}

				if err != nil {
					return fmt.Errorf("error reading input: %v", err)
				}
				input.WriteString(currentLineStr)

			} else {
				currentLineStr, err := reader.ReadString('\n')
				if err != nil {
					return fmt.Errorf("error reading input: %v", err)
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

	ProcessStatement:
		currentScopeDepth = 0

		// Clean up input
		inputStr := input.String()
		if inputStr == "" {
			continue
		}
		if strings.ToLower(inputStr) == "exit" {
			return nil
		}

		// Execute the code
		msg, signal, err := ExecuteCodeAndReturnMessageSliceGivenSettings(inputStr, parserEnv, executor)
		if err != nil || signal != glob.SysSignalTrue {
			printMessagesToWriter(writer, msg)
			fmt.Fprintf(writer, "---\n[Warning] failed :(\n")
			continue
		}

		// Print results
		printMessagesToWriter(writer, msg)
		fmt.Fprintln(writer, "---\nsuccess! :)")
	}
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
	parserEnv := parser.NewParserEnv()
	executor := exe.NewExecutor(env.NewEnv(nil, nil))
	reader := bufio.NewReader(os.Stdin)

	fmt.Println("Litex-beta - Type your code or 'exit' to quit\nWarning: not yet ready for production use.")

	err := listen(reader, os.Stdout, parserEnv, executor)
	if err != nil {
		fmt.Printf("Error: %v\n", err)
	}

	fmt.Println("Goodbye!")
}
