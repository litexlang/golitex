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

package litex_sys

import (
	"fmt"
	"testing"
)

func TestRunFile(t *testing.T) {
	msg, signal, err := RunFile("../litex_code_examples/litex_as_regex_matcher.lix")
	if err != nil {
		t.Errorf(err.Error())
	}
	fmt.Println(msg)
	fmt.Println(signal)
}

func TestRunREPLInTerminal(t *testing.T) {
	RunREPLInTerminal()
}
