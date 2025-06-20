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

func TestRunRepo(t *testing.T) {
	msg, signal, err := RunRepo("../examples/number_theory_for_beginners_by_andre_weil")
	if err != nil {
		t.Errorf(err.Error())
	}
	fmt.Println(msg)
	fmt.Println(signal)
}

func TestRunFileInRepo(t *testing.T) {
	msg, signal, err := RunFile("../examples/number_theory_for_beginners_by_andre_weil/chap6.lix")
	if err != nil {
		t.Errorf(err.Error())
	}
	fmt.Println(msg)
	fmt.Println(signal)
}

func TestRunAllComprehensiveCodes(t *testing.T) {
	pathSlice := []string{
		"../examples/comprehensive_examples",
		"../examples/testings",
	}

	for _, path := range pathSlice {
		err := RunFilesInRepo(path)
		if err != nil {
			fmt.Println("Error running files:", err)
			return
		}
	}
}
