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
	curEnv := env.NewEnv(nil)
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

func main() {
	parserEnv := parser.NewParserEnv()
	executor := exe.NewExecutor(env.NewEnv(nil))

	reader := bufio.NewReader(os.Stdin)
	fmt.Println("REPL - Type your code or 'exit' to quit")

	for {
		fmt.Print(">>> ")
		input, err := reader.ReadString('\n')
		if err != nil {
			fmt.Println("Error reading input:", err)
			continue
		}

		// Clean up input
		input = strings.TrimSpace(input)
		if input == "" {
			continue
		}
		if strings.ToLower(input) == "exit" {
			break
		}

		// Execute the code
		msg, signal, err := ExecuteCodeAndReturnMessageSliceGivenSettings(input, parserEnv, executor)
		if err != nil {
			fmt.Printf("[ERROR] %v\n", err)
			continue
		}

		// Print results
		if msg != nil && len(msg) > 0 {
			fmt.Println(msg)
		}

		if signal != glob.SysSignalTrue {
			fmt.Printf("Warning: [%s] is not true\n", input)
		}
	}

	fmt.Println("Goodbye!")
}
