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
	"bytes"
	"fmt"
	"os"
	"os/exec"
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

func runComprehensiveCodesInTerminal(path string) error {
	// Get the path to the .lix file (equivalent to the Python code)
	// exe, err := os.Executable()
	// if err != nil {
	// 	fmt.Println("Error getting executable path:", err)
	// 	return
	// }

	// Construct the path to the .lix file
	// path := filepath.Join(filepath.Dir(exe), "..", "examples", "comprehensive_examples", "Hilbert_geometry_axioms_formalization.lix")

	// Read the file content
	code, err := os.ReadFile(path)
	if err != nil {
		fmt.Println("Error reading file:", err)
		return err
	}

	// Execute the command (assuming main.go is in the same directory)

	cmd := exec.Command("go", "run", "../main.go", "-e", string(code))

	// Capture both stdout and stderr
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr

	// Run the command
	err = cmd.Run()
	if err != nil {
		fmt.Println("Error running command:", err)
		fmt.Println("Stderr:", stderr.String())
		return err
	}

	// Print the output
	fmt.Println("Output:", stdout.String())
	return nil
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
		if err != nil {
			fmt.Println("Error executing code:", err)
			return
		}
		if signal != glob.SysSignalTrue {
			fmt.Println(msg)
			fmt.Println("Error in file:", file.Name())
			return
		}
	}

	fmt.Println("All codes executed successfully")
}
