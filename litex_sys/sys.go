// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_sys

import (
	glob "golitex/litex_global"
	pipeline "golitex/litex_pipeline"
	"os"
)

func RunFile(path string) (string, glob.SysSignal, error) {
	content, err := os.ReadFile(path)
	if err != nil {
		return "", glob.SysSignalParseError, err
	}
	msg, signal, err := pipeline.ExecuteCodeAndReturnMessage(string(content))
	if err != nil {
		return "", signal, err
	}
	return msg, signal, nil
}

func ExecString(code string) (string, glob.SysSignal, error) {
	msg, signal, err := pipeline.ExecuteCodeAndReturnMessage(code)
	if err != nil {
		return "", signal, err
	}
	return msg, signal, nil
}
