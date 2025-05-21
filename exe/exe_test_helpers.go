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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
	parser "golitex/parser"
	"os"
	"strings"
)

func setupAndParseStmtTest(code string, parserEnv *parser.ParserEnv) []ast.TopStmt {
	topStatements, err := parser.ParseSourceCode(code, parserEnv)
	if err != nil {
		panic(err)
	}
	return topStatements
}

func execStmtTest(topStmt []ast.TopStmt) []string {
	env := env.NewEnv(nil, nil)
	executor := *NewExecutor(env)

	messages := []string{}
	var notTrueMessageBuilder strings.Builder
	notTrueMessageBuilder.WriteString("execution is not true at:\n\n")

	isNotTrue := false

	for _, topStmt := range topStmt {
		execState, err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			panic(err)
		}

		if execState != glob.ExecState_True && !glob.ContinueExecutionIfExecUnknown {
			isNotTrue = true
			notTrueMessageBuilder.WriteString(topStmt.String())
			notTrueMessageBuilder.WriteString("\n\n")
			break
		}

		// 如果连续两个 \n 则删除一个
		var newMsgs []string
		for i := 0; i < len(executor.env.Msgs); i++ {
			if i < len(executor.env.Msgs)-1 && executor.env.Msgs[i] == "\n" && executor.env.Msgs[i+1] == "\n" {
				newMsgs = append(newMsgs, executor.env.Msgs[i])
				i++ // Skip the next newline
			} else {
				newMsgs = append(newMsgs, executor.env.Msgs[i])
			}
		}
		executor.env.Msgs = newMsgs

		messages = append(messages, strings.Join(executor.env.Msgs, "\n"))
	}

	if isNotTrue {
		messages = append(messages, notTrueMessageBuilder.String())
	} else {
		messages = append(messages, "---\nexecution success! :)")
	}

	return messages
}

func readFile(filePath string) string {
	content, err := os.ReadFile(filePath)
	if err != nil {
		panic(err)
	}
	return string(content)
}

func printExecMsg(messageSlice []string) {
	for _, msg := range messageSlice {
		fmt.Println(msg)
	}
}
