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
	"testing"
	"time"
)

func TestWholeFile(t *testing.T) {
	start := time.Now()
	// codePath := readFile("../examples/comprehensive_examples/syllogism.lix")
	// codePath := readFile("../examples/comprehensive_examples/Hilbert_geometry_axioms_formalization.lix")
	// codePath := readFile("../examples/comprehensive_examples/multivariate_linear_equation.lix")
	// codePath := readFile("../examples/comprehensive_examples/algorithm.lix")
	// codePath := readFile("../examples/comprehensive_examples/syllogism.lix")
	// codePath := readFile("../examples/test_codes/match_env.lix")
	// codePath := readFile("../examples/number_theory_for_beginners_by_andre_weil/number_theory_for_beginners_by_andre_weil.lix")
	// codePath := readFile("../examples/test_codes/tmp.lix")
	// codePath := readFile("../examples/number_theory_for_beginners_by_andre_weil/version1.lix")
	// codePath := readFile("../examples/test_codes/claim.lix")
	// codePath := readFile("../examples/test_codes/import.lix")
	codePath := "../examples/test_codes/tmp.lix"
	readFileTime := time.Since(start)
	start = time.Now()
	topStmtSlice := setupAndParseStmtTest(codePath)
	parseTime := time.Since(start)
	start = time.Now()
	messages := execStmtTest(topStmtSlice)
	executionTime := time.Since(start)
	printExecMsg(messages)
	fmt.Printf("read file takes %v\nparsing takes %v\nexecution takes %v\n", readFileTime, parseTime, executionTime)
}
