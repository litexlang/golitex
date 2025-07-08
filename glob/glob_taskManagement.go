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

var AllowImport bool = true

// 存储当前的传入的repo的repo名
var CurrentTaskDirName string = ""
var PreviousTaskDirNameSlice []string = []string{}

var CurrentPkg string = ""
var PreviousPkgSlice []string = []string{}
var DeclaredPkgNames = map[string]struct{}{"": {}}
var IsRunningPipelineInit bool = false

func ImportDirStmtInit(newPkg string, path string) error {
	PreviousTaskDirNameSlice = append(PreviousTaskDirNameSlice, CurrentTaskDirName)
	CurrentTaskDirName = filepath.Join(CurrentTaskDirName, path)

	PreviousPkgSlice = append(PreviousPkgSlice, CurrentPkg)
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
	return nil
}

func ImportDirStmtEnd() {
	CurrentPkg = PreviousPkgSlice[len(PreviousPkgSlice)-1]
	PreviousPkgSlice = PreviousPkgSlice[:len(PreviousPkgSlice)-1]
	CurrentTaskDirName = PreviousTaskDirNameSlice[len(PreviousTaskDirNameSlice)-1]
	PreviousTaskDirNameSlice = PreviousTaskDirNameSlice[:len(PreviousTaskDirNameSlice)-1]
}

func RequireMsg() bool {
	return len(PreviousPkgSlice) == 0 && !IsRunningPipelineInit
}
