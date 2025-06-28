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

package litex_global

import (
	"fmt"
	"path/filepath"
	"strings"
)

// 存储当前的传入的repo的repo名
var CurrentTaskDirName string = ""
var previousTaskDirNameSlice []string = []string{}

var CurrentPkg string = ""
var previousPkgSlice []string = []string{}
var DeclaredPkgNames = map[string]struct{}{"": {}}

func ImportStmtInit(newPkg string, path string) error {
	previousTaskDirNameSlice = append(previousTaskDirNameSlice, CurrentTaskDirName)
	CurrentTaskDirName = filepath.Join(CurrentTaskDirName, path)

	previousPkgSlice = append(previousPkgSlice, CurrentPkg)
	if newPkg != "" {
		if CurrentPkg == "" {
			CurrentPkg = newPkg
		} else {
			CurrentPkg = strings.Join([]string{CurrentPkg, newPkg}, KeySymbolColonColon)
		}
		// import name should be valid
		err := IsValidUseDefinedFcAtom(newPkg)
		if err != nil {
			return err
		}

		if _, ok := DeclaredPkgNames[CurrentPkg]; !ok {
			DeclaredPkgNames[CurrentPkg] = struct{}{}
		} else {
			return fmt.Errorf("duplicate package name: '%s'", CurrentPkg)
		}
	}
	return nil
}

func ImportStmtEnd() {
	CurrentPkg = previousPkgSlice[len(previousPkgSlice)-1]
	previousPkgSlice = previousPkgSlice[:len(previousPkgSlice)-1]
	CurrentTaskDirName = previousTaskDirNameSlice[len(previousTaskDirNameSlice)-1]
	previousTaskDirNameSlice = previousTaskDirNameSlice[:len(previousTaskDirNameSlice)-1]
}

func IsNotImportState() bool {
	return len(previousPkgSlice) == 0
}
