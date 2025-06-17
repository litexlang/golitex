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
	glob "golitex/glob"
	pipeline "golitex/pipeline"
	"os"
	"path/filepath"
	"strings"

	taskManager "golitex/task_manager"
)

func RunFile(path string) (string, glob.SysSignal, error) {
	// 得到path的repo名所在的绝对路径
	repoName := filepath.Dir(path)
	taskManager.TaskRepoName = repoName
	content, err := os.ReadFile(path)
	if err != nil {
		return "", glob.SysSignalParseError, err
	}
	msg, signal, err := pipeline.ExecuteCodeAndReturnMessage(string(content))
	if err != nil {
		return msg, signal, err
	}
	return msg, signal, nil
}

func RunRepo(path string) (string, glob.SysSignal, error) {
	taskManager.TaskRepoName = path
	// 运行里面的main.lix
	content, err := os.ReadFile(filepath.Join(path, "main.lix"))
	if err != nil {
		return "", glob.SysSignalParseError, err
	}
	msg, signal, err := pipeline.ExecuteCodeAndReturnMessage(string(content))
	if err != nil {
		return msg, signal, err
	}
	return msg, signal, nil
}

func ExecuteCodeAndReturnMessage(code string) (string, glob.SysSignal, error) {
	msg, signal, err := pipeline.ExecuteCodeAndReturnMessage(code)
	if err != nil {
		return msg, signal, err
	}
	return msg, signal, nil
}

func BetterMsg(msg string) string {
	// 把超过一个的 \n 变成一个 (可能是3个，可能是2个，可能多个)
	msg = strings.ReplaceAll(msg, "\n\n", "\n")
	return msg
}

func RunREPLInTerminal() {
	pipeline.RunREPLInTerminal()
}
