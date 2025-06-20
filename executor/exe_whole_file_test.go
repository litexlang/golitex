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
// Litex Zulip community: https://litex.zulipchat.com

package litex_executor

import (
	"fmt"
	"testing"
	"time"
)

func TestWholeFile(t *testing.T) {
	start := time.Now()
	// codePath := "../examples/test_codes/builtin_cmp.lix"
	codePath := "../examples/test_codes/tmp.lix"
	readFileTime := time.Since(start)
	start = time.Now()
	topStmtSlice, err := setupAndParseStmtTest(codePath)
	if err != nil {
		t.Errorf(err.Error())
		return
	}
	parseTime := time.Since(start)
	start = time.Now()
	messages := execStmtTest(topStmtSlice)
	executionTime := time.Since(start)
	printExecMsg(messages)
	fmt.Printf("read file takes %v\nparsing takes %v\nexecution takes %v\n", readFileTime, parseTime, executionTime)
}
