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

package litex_pipeline

import (
	"fmt"
	"os"
	"testing"
)

func TestExecuteCodeAndReturnMessage(t *testing.T) {
	code := readFile("../examples/test_codes/tmp.lit")
	executor, err := InitPipelineExecutor()
	if err != nil {
		t.Errorf("Error: %s", err)
	}
	ret := RunSourceCodeInExecutor(executor, code)
	if ret.IsNotTrue() {
		t.Errorf("Error: %s", ret.String())
	}
	fmt.Println(ret.String())
}

func readFile(filePath string) string {
	content, err := os.ReadFile(filePath)
	if err != nil {
		panic(err)
	}
	return string(content)
}
