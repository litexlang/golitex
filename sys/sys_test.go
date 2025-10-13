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
	"time"
)

func TestRunREPLInTerminal(t *testing.T) {
	RunREPLInTerminal("test_version")
}

func TestRunRepo(t *testing.T) {
	msg, signal, err := RunRepo("../examples/test_import")
	if err != nil {
		t.Errorf(err.Error())
	}
	fmt.Println(msg)
	fmt.Println(signal)
}

func TestRunFileInRepo(t *testing.T) {
	startTime := time.Now()
	msg, signal, err := RunFile("../examples/test_codes/natural_numbers1.lit")
	if err != nil {
		t.Errorf(err.Error())
	}
	fmt.Println(msg)
	fmt.Println(signal)
	executionTime := time.Since(startTime)
	fmt.Printf("execution time: %s\n", executionTime)
}
