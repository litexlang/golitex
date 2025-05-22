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
	"testing"
	"time"

	parser "golitex/parser"
)

func TestWholeFile(t *testing.T) {
	start := time.Now()
	// code := readFile("../examples/comprehensive_examples/working_hilbert_geometry.lix")
	code := readFile("../examples/test_codes/match_env.lix")
	readFileTime := time.Since(start)
	start = time.Now()
	topStmtSlice := setupAndParseStmtTest(code, &parser.ParserEnv{})
	parseTime := time.Since(start)
	start = time.Now()
	messages := execStmtTest(topStmtSlice)
	executionTime := time.Since(start)
	printExecMsg(messages)
	fmt.Printf("read file takes %v\nparsing takes %v\nexecution takes %v\n", readFileTime, parseTime, executionTime)
}
