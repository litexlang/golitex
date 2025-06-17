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
	"os"
	"testing"

	glob "golitex/glob"
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

func TestRunAllComprehensiveCodes(t *testing.T) {
	files, err := os.ReadDir("../examples/comprehensive_examples")
	if err != nil {
		fmt.Println("Error reading directory:", err)
		return
	}

	for _, file := range files {
		// 读出file的内容，然后执行
		code, err := os.ReadFile("../examples/comprehensive_examples/" + file.Name())
		if err != nil {
			fmt.Println("Error reading file:", err)
			return
		}
		msg, signal, err := ExecuteCodeAndReturnMessage(string(code))
		if err != nil || signal != glob.SysSignalTrue {
			fmt.Println(msg)
			fmt.Println("Error executing code:", err)
			fmt.Println("Error in file:", file.Name())
			return
		}
	}

	fmt.Println("All codes executed successfully")
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
