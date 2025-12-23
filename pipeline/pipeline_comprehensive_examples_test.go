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
	ast "golitex/ast"
	env "golitex/environment"
	exe "golitex/executor"
	glob "golitex/glob"
	pkgMgr "golitex/package_manager"
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

	start := time.Now()

	for _, path := range pathSlice {
		err := RunFilesInRepoWithPipelineRunner(path)
		if err != nil {
			panic(fmt.Sprintf("Error running files: %s", err))
		}
	}

	elapsed := time.Since(start)
	fmt.Printf("All Files Take %s\n", elapsed)
}

func RunFilesInRepoWithPipelineRunner(repo string) error {
	files, err := os.ReadDir(repo)
	if err != nil {
		fmt.Println("Error reading directory:", err)
		return err
	}

	allFilesStartTime := time.Now()

	// 每次打开文件时重启 executor
	envPkgMgr := env.NewPkgMgr(repo, "")

	envMgr, err := NewBuiltinEnvMgrWithNewEmptyEnv(envPkgMgr)
	if err != nil {
		return fmt.Errorf("failed to init pipeline env: %s", err)
	}

	executor := exe.NewExecutor(envMgr)

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

		pkgPathNameMgr := pkgMgr.NewEmptyPkgMgr()

		// Run the code directly
		topStmtSlice, err := ast.ParseSourceCode(string(content), pkgPathNameMgr)
		if err != nil {
			return fmt.Errorf("parse error in file %s: %s", file.Name(), err.Error())
		}

		for _, topStmt := range topStmtSlice {
			execState := executor.Stmt(topStmt)
			if execState.IsErr() {
				return fmt.Errorf("\n\nexecution test failed in file %s, line %d:\n%s\n\n", file.Name(), topStmt.GetLine(), execState.String())
			}
			if execState.IsUnknown() {
				return fmt.Errorf("\n\nexecution test failed in file %s, line %d: unknown:\n%s\n\n", file.Name(), topStmt.GetLine(), execState.String())
			}
		}

		elapsed := time.Since(start)

		fmt.Printf("%s\n", elapsed)

		executor.ClearStmt()

	}

	fmt.Printf("All Files Take %s\n", time.Since(allFilesStartTime))

	return nil
}
