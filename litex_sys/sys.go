// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_sys

import (
	pipeline "golitex/litex_pipeline"
	"os"
)

func ExecFileReturnString(path string) (string, error) {
	content, err := os.ReadFile(path)
	if err != nil {
		return "", err
	}
	return pipeline.ExecuteCodeAndReturnMessage(string(content))
}

func ExecString(code string) (string, error) {
	return pipeline.ExecuteCodeAndReturnMessage(code)
}
