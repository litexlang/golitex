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
	"fmt"
	glob "golitex/glob"
	pipeline "golitex/pipeline"
	"os"
	"path/filepath"
	"strings"
	"time"
)

func RunFile(path string) (string, glob.SysSignal, error) {
	// 得到path的repo名所在的绝对路径
	// repoName := filepath.Dir(path)
	// glob.CurrentTaskDirName = repoName
	content, err := os.ReadFile(path)
	if err != nil {
		return fmt.Sprintf("failed to read file %s: %s", path, err.Error()), glob.SysSignalSystemError, err
	}
	msg, signal, _, err := pipeline.RunSourceCode(nil, string(content))
	if err != nil {
		return msg, signal, err
	}
	return msg, signal, nil
}

func RunFileWithPipelineRunner(path string) (string, glob.SysSignal, time.Duration, error) {
	// repoName := filepath.Dir(path)
	// glob.CurrentTaskDirName = repoName
	content, err := os.ReadFile(path)
	if err != nil {
		return fmt.Sprintf("failed to read file %s: %s", path, err.Error()), glob.SysSignalSystemError, 0, err
	}
	pipelineRunner := pipeline.NewPipelineRunner()

	start := time.Now()
	msg, signal, err := pipelineRunner.Run(string(content))
	if err != nil {
		return fmt.Sprintf("%s\n%s", msg, err.Error()), glob.SysSignalSystemError, 0, err
	}
	return msg, signal, time.Since(start), nil
}

func RunRepo(path string) (string, glob.SysSignal, error) {
	// glob.CurrentTaskDirName = path
	// 运行里面的main.lit
	content, err := os.ReadFile(filepath.Join(path, glob.PkgEntranceFileName))
	if err != nil {
		return "", glob.SysSignalSystemError, err
	}
	msg, signal, _, err := pipeline.RunSourceCode(nil, string(content))
	if err != nil {
		return msg, signal, err
	}
	return msg, signal, nil
}

func ExecuteCodeAndReturnMessage(code string) (string, glob.SysSignal, error) {
	msg, signal, _, err := pipeline.RunSourceCode(nil, code)
	if err != nil {
		return msg, signal, err
	}
	return msg, signal, nil
}

func RunREPLInTerminal(version string) {
	pipeline.RunREPLInTerminal(version)
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
		// file 最后必须以.lit结尾
		localStartTime := time.Now()

		if !strings.HasSuffix(file.Name(), glob.LitexFileSuffix) {
			continue
		}

		fmt.Printf("%s ", file)

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

		localElapsed := time.Since(localStartTime)

		fmt.Printf("%s\n", localElapsed)
	}
	elapsed := time.Since(startTime)
	fmt.Printf("All files in %s executed successfully\n", repo)
	fmt.Println("Time taken:", elapsed)

	return nil
}

func RunFilesInRepoWithPipelineRunner(repo string) error {
	files, err := os.ReadDir(repo)
	if err != nil {
		fmt.Println("Error reading directory:", err)
		return err
	}

	pipelineRunner := pipeline.NewPipelineRunner()

	allFilesStartTime := time.Now()

	for _, file := range files {
		// file 最后必须以.lit结尾

		if !strings.HasSuffix(file.Name(), glob.LitexFileSuffix) {
			continue
		}

		fmt.Printf("%s ", file)

		// 读出file的内容，然后执行
		path := filepath.Join(repo, file.Name())

		content, err := os.ReadFile(path)
		if err != nil {
			fmt.Println("Error reading file:", err)
			return err
		}

		start := time.Now()
		msg, signal, err := pipelineRunner.Run(string(content))
		if err != nil || signal != glob.SysSignalTrue {
			return fmt.Errorf("%s\n%s\nerror in file: %s", msg, err.Error(), file.Name())
		}

		elapsed := time.Since(start)

		fmt.Printf("%s\n", elapsed)

		pipelineRunner.Clear()
	}

	fmt.Printf("All Files Take %s\n", time.Since(allFilesStartTime))

	return nil
}
