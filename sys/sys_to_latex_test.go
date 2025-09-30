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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_sys

import (
	"fmt"
	"os"
	"testing"
	"time"
)

func Test_ToLatex(t *testing.T) {
	startTime := time.Now()
	fileName := "../examples/test_codes/tmp.lit"
	msg, signal, err := CompileFileToLatex(fileName)
	if err != nil {
		t.Errorf("failed to run file %s\n", fileName)
	}

	fmt.Println(msg)

	// 把msg写入到文件
	writeTo := "../past_examples/test_to_latex.tex"
	os.WriteFile(writeTo, []byte(msg), 0644)
	fmt.Printf("write to %s\n", writeTo)

	fmt.Println(signal)
	executionTime := time.Since(startTime)
	fmt.Printf("execution time: %s\n", executionTime)
}
