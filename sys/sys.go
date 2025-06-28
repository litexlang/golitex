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
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_sys

import (
	"fmt"
	glob "golitex/glob"
	pipeline "golitex/pipeline"
	"os"
	"path/filepath"
	"time"
)

func RunFile(path string) (string, glob.SysSignal, error) {
	// 得到path的repo名所在的绝对路径
	repoName := filepath.Dir(path)
	glob.CurrentTaskDirName = repoName
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
	glob.CurrentTaskDirName = path
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

func PostprocessOutputMsg(msg string) string {
	// 把超过一个的 \n 变成一个 (可能是3个，可能是2个，可能多个)
	// msg = strings.ReplaceAll(msg, "\n\n", "\n")
	return msg
}

func RunREPLInTerminal() {
	pipeline.RunREPLInTerminal()
}

func RunMainMsg(signal glob.SysSignal) string {
	if signal == glob.SysSignalTrue {
		return glob.REPLSuccessMessage
	} else if signal == glob.SysSignalFalse {
		return glob.REPLFailedMessage
	} else {
		return glob.REPLFailedMessage
	}
}

func RunFilesInRepo(repo string) error {
	files, err := os.ReadDir(repo)
	if err != nil {
		fmt.Println("Error reading directory:", err)
		return err
	}

	startTime := time.Now()
	for _, file := range files {
		// 读出file的内容，然后执行
		path := filepath.Join(repo, file.Name())
		code, err := os.ReadFile(path)
		if err != nil {
			fmt.Println("Error reading file:", err)
			return err
		}
		msg, signal, err := ExecuteCodeAndReturnMessage(string(code))
		if err != nil || signal != glob.SysSignalTrue {
			fmt.Println(msg)
			fmt.Println("Error executing code:", err)
			return fmt.Errorf("error in file: %s", file.Name())
		}
	}
	elapsed := time.Since(startTime)
	fmt.Printf("All files in %s executed successfully\n", repo)
	fmt.Println("Time taken:", elapsed)

	return nil
}
