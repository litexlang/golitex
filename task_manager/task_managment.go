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

package litex_task_manager

import "fmt"

// 存储当前的传入的repo的repo名
var TaskRepoName string

var CurrentPkg string = ""
var previousPkg string = ""
var DeclaredPkgNames = map[string]struct{}{"": {}}
var ImportMode bool = false

func ImportStmtInit(newPkg string) error {
	ImportMode = true

	previousPkg = CurrentPkg
	CurrentPkg = newPkg
	if _, ok := DeclaredPkgNames[newPkg]; !ok {
		DeclaredPkgNames[newPkg] = struct{}{}
	} else {
		return fmt.Errorf("duplicate package name: '%s'", newPkg)
	}
	return nil
}

func ImportStmtEnd() {
	ImportMode = false

	CurrentPkg = previousPkg
}
