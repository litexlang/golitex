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

// func RunFile(path string) (string, glob.SysSignal, error) {
// 	content, err := os.ReadFile(path)
// 	if err != nil {
// 		return fmt.Sprintf("failed to read file %s: %s", path, err.Error()), glob.SysSignalSystemError, err
// 	}
// 	ret := pipeline.RunSourceCode(string(content))
// 	return ret.String(), ret.SysSignal(), ret.Error()
// }

func RunFileWithPipelineRunner(path string) (glob.GlobRet, time.Duration, error) {
	// repoName := filepath.Dir(path)
	// glob.CurrentTaskDirName = repoName
	content, err := os.ReadFile(path)
	if err != nil {
		return glob.NewGlobErr(fmt.Sprintf("failed to read file %s: %s", path, err.Error())), 0, err
	}
	pipelineRunner := pipeline.NewPipelineRunner()

	start := time.Now()
	ret := pipelineRunner.Run(string(content))
	if ret.IsErr() {
		return ret, 0, ret.Error()
	}
	return ret, time.Since(start), nil
}

func RunRepo(path string) (glob.GlobRet, error) {
	// glob.CurrentTaskDirName = path
	// 运行里面的main.lit
	content, err := os.ReadFile(filepath.Join(path, glob.PkgEntranceFileNameMainDotLit))
	if err != nil {
		return glob.NewGlobErr(err.Error()), err
	}
	ret := pipeline.RunSourceCode(string(content))
	return ret, ret.Error()
}

// func ExecuteCodeAndReturnMessage(code string) (string, glob.SysSignal, error) {
// 	ret := pipeline.RunSourceCode(code)
// 	return ret.String(), ret.SysSignal(), ret.Error()
// }

func RunREPLInTerminal(version string) {
	pipeline.RunREPLInTerminal(version)
}

func RunMainMsg(ret glob.GlobRet) string {
	if ret.IsTrue() {
		return glob.REPLSuccessMessage
	}
	return glob.REPLFailedMessage
}

// func RunFilesInRepo(repo string) error {
// 	files, err := os.ReadDir(repo)
// 	if err != nil {
// 		fmt.Println("Error reading directory:", err)
// 		return err
// 	}

// 	startTime := time.Now()
// 	for _, file := range files {
// 		// file 最后必须以.lit结尾
// 		localStartTime := time.Now()

// 		if !strings.HasSuffix(file.Name(), glob.LitexFileSuffix) {
// 			continue
// 		}

// 		fmt.Printf("%s ", file)

// 		// 读出file的内容，然后执行
// 		path := filepath.Join(repo, file.Name())
// 		code, err := os.ReadFile(path)
// 		if err != nil {
// 			fmt.Println("Error reading file:", err)
// 			return err
// 		}
// 		msg, signal, err := ExecuteCodeAndReturnMessage(string(code))
// 		if err != nil || signal != glob.SysSignalTrue {
// 			fmt.Println(msg)
// 			fmt.Println("Error executing code:", err)
// 			return fmt.Errorf("error in file: %s", file.Name())
// 		}

// 		localElapsed := time.Since(localStartTime)

// 		fmt.Printf("%s\n", localElapsed)
// 	}
// 	elapsed := time.Since(startTime)
// 	fmt.Printf("All files in %s executed successfully\n", repo)
// 	fmt.Println("Time taken:", elapsed)

// 	return nil
// }

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
		ret := pipelineRunner.Run(string(content))
		if ret.IsNotTrue() {
			err := ret.Error()
			if err == nil {
				err = fmt.Errorf("execution failed")
			}
			return fmt.Errorf("%s\n%s\nerror in file: %s", ret.String(), err.Error(), file.Name())
		}

		elapsed := time.Since(start)

		fmt.Printf("%s\n", elapsed)

		pipelineRunner.Clear()
	}

	fmt.Printf("All Files Take %s\n", time.Since(allFilesStartTime))

	return nil
}
