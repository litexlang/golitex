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
	"fmt"
	env "golitex/litex_env"
	exe "golitex/litex_executor"
	glob "golitex/litex_global"
	parser "golitex/litex_parser"
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
	topStmtSlice, err := parser.ParseSourceCode(code)
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
