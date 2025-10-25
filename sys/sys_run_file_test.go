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
	"testing"
)

func Test_File(t *testing.T) {
	fileName := "../examples/test_codes/tmp.lit"
	// msg, signal, err := RunFile(fileName)
	msg, signal, elapsed, err := RunFileWithPipelineRunner(fileName)
	if err != nil {
		t.Errorf("failed to run file %s\n", fileName)
	}
	fmt.Println(msg)
	fmt.Println(signal)
	fmt.Printf("elapsed time: %s\n", elapsed)
}
