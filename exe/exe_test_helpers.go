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

	isNotTrue := false

	for _, topStmt := range topStmt {
		execState, err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			messages = append(messages, err.Error())
			return messages
		}

		if execState != glob.ExecState_True && !glob.ContinueExecutionIfExecUnknown {
			isNotTrue = true
			// notTrueMessageBuilder.WriteString(topStmt.String())
			// notTrueMessageBuilder.WriteString("\n\n")
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

		if isNotTrue {
			messages = append(messages, fmt.Sprintf("execution is not true at:\n\n%s", topStmt.String()))
			break
		}
	}

	if isNotTrue {
		messages = append(messages, fmt.Sprintf("---\n%s", glob.REPLFailedMessage))
	} else {
		messages = append(messages, fmt.Sprintf("---\n%s", glob.REPLSuccessMessage))
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
	// 如果上一个msg是 \n ，或者上一行终止以 \n 结尾，则这一行是纯\n的话，则删除这一行
	lastMsgIsNewline := false
	for _, msg := range messageSlice {
		if lastMsgIsNewline {
			if strings.TrimSpace(msg) == "" {
				continue
			}
		}

		if strings.HasSuffix(msg, "\n\n") {
			msg = strings.TrimSpace(msg)
			msg = fmt.Sprintf("%s\n", msg)
		}

		lastMsgIsNewline = strings.HasSuffix(msg, "\n")
		fmt.Println(msg)
	}
}
