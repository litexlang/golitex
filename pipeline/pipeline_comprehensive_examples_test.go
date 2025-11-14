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
	glob "golitex/glob"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func Test_ComprehensiveCodes(t *testing.T) {
	pathSlice := []string{
		"../examples/comprehensive_examples",
		"../examples/testings",
	}

	for _, path := range pathSlice {
		err := RunFilesInRepoWithPipelineRunner(path)
		if err != nil {
			panic(fmt.Sprintf("Error running files: %s", err))
		}
	}
}

func RunFilesInRepoWithPipelineRunner(repo string) error {
	files, err := os.ReadDir(repo)
	if err != nil {
		fmt.Println("Error reading directory:", err)
		return err
	}

	pipelineRunner := NewPipelineRunner()

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
