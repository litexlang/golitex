// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

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
				fmt.Fprint(writer, strings.Repeat(" ", 4*currentScopeDepth))
			}

			currentLineStr, err := reader.ReadString('\n')
			if err != nil {
				return fmt.Errorf("error reading input: %v", err)
			}
			input.WriteString(currentLineStr)

			// input 的非空白的最后一位 不是 :
			trimmedLine := strings.TrimSpace(currentLineStr)
			if trimmedLine == "" || !strings.HasSuffix(trimmedLine, ":") {
				break
			} else {
				currentScopeDepth += 1
			}
		}

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
		if err != nil {
			fmt.Fprintf(writer, "[ERROR] %v\n", err)
			continue
		}

		// Print results
		if len(msg) > 0 {
			for _, m := range msg {
				fmt.Fprintln(writer, m)
			}
		}

		if signal != glob.SysSignalTrue {
			fmt.Fprintf(writer, "Warning: [%s] is not true\n", input)
		}
	}
}

func RunREPLInTerminal() {
	parserEnv := parser.NewParserEnv()
	executor := exe.NewExecutor(env.NewEnv(nil, nil))
	reader := bufio.NewReader(os.Stdin)

	fmt.Println("Litex 0.0.1-beta - Type your code or 'exit' to quit")

	err := listen(reader, os.Stdout, parserEnv, executor)
	if err != nil {
		fmt.Printf("Error: %v\n", err)
	}

	fmt.Println("Goodbye!")
}
