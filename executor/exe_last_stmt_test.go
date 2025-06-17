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
	"strings"
	"testing"
	"time"

	parser "golitex/parser"
)

func TestLastStmt(t *testing.T) {
	start := time.Now()
	allCode := readFile("../examples/test_codes/tmp.lix")
	code := extractFromLastProveLine(allCode)
	readFileTime := time.Since(start)
	start = time.Now()
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		panic(err)
	}
	parseTime := time.Since(start)
	start = time.Now()
	var messages []string
	if len(topStmtSlice) == 0 {
		fmt.Println("nothing to execute")
	} else {
		messages = execStmtTest(topStmtSlice[len(topStmtSlice)-1:])
	}
	executionTime := time.Since(start)
	printExecMsg(messages)
	fmt.Printf("get last top stmt takes %v\nparsing takes %v\nexecution takes %v\n", readFileTime, parseTime, executionTime)
}

func extractFromLastProveLine(content string) string {
	lines := strings.Split(content, "\n")
	lastIndex := -1

	for i, line := range lines {
		if strings.HasPrefix(line, "prove:") {
			lastIndex = i
		}
	}

	if lastIndex == -1 {
		return "" // 没有找到
	}

	// 从最后一个匹配的行开始到末尾
	return strings.Join(lines[lastIndex:], "\n")
}
