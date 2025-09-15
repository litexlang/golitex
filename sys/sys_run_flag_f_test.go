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
	"bytes"
	"fmt"
	"os/exec"
	"testing"
)

func TestRunFileInTerminalFlagF(t *testing.T) {
	path := "../examples/test_codes/tmp.lix"

	cmd := exec.Command("go", "run", "../main.go", "-f", path)

	// Capture both stdout and stderr
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr

	// Run the command
	err := cmd.Run()
	if err != nil {
		fmt.Println("Error running command:", err)
		fmt.Println("Stderr:", stderr.String())
		return
	}

	// Print the output
	fmt.Println(stdout.String())
}
