// Copyright Jiachen Shen.
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
	package_manager "golitex/package_manager"
	"os"
	"path/filepath"
	"testing"
	"time"
)

func Test_File(t *testing.T) {
	fileName := "../examples/test_codes/tmp.lit"
	workingDir, err := os.Getwd()
	if err != nil { //
		t.Errorf("failed to get current working directory: %v\n", err)
	}
	absOfFile := filepath.Join(workingDir, fileName)
	start := time.Now()
	pkgMgr := package_manager.NewEmptyPkgMgr(workingDir)
	_, retType, rets := RunFileInPkgMgr(absOfFile, "", pkgMgr, false)

	for _, ret := range rets {

		fmt.Println(glob.StringWithOptimizedNewline(ret.String()))
	}

	fmt.Println(glob.REPLMsg(retType))
	executionTime := time.Since(start)
	fmt.Printf("execution time: %s\n", executionTime)
}

func Test_ImportFile(t *testing.T) {
	fileName := "../examples/test_import/main.lit"
	workingDir, err := os.Getwd()
	if err != nil {
		t.Errorf("failed to get current working directory: %v\n", err)
	}
	absOfFile := filepath.Join(workingDir, fileName)
	start := time.Now()
	pkgMgr := package_manager.NewEmptyPkgMgr(workingDir)
	_, retType, rets := RunFileInPkgMgr(absOfFile, "", pkgMgr, false)
	for _, ret := range rets {
		fmt.Println(glob.StringWithOptimizedNewline(ret.String()))
	}
	fmt.Println(glob.REPLMsg(retType))
	executionTime := time.Since(start)
	fmt.Printf("execution time: %s\n", executionTime)
}
