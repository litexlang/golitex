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
	env "golitex/environment"
	glob "golitex/glob"
	"os"
)

type PackagesManager struct {
	pkgEnv map[string]*env.Env
}

func NewPackageManager() *PackagesManager {
	return &PackagesManager{
		pkgEnv: make(map[string]*env.Env),
	}
}

func (pkgMgr *PackagesManager) NewPkg(builtinEnv *env.Env, path string) (string, glob.SysSignal, error) {
	if _, ok := pkgMgr.pkgEnv[path]; ok {
		return fmt.Sprintf("%s is already imported", path), glob.SysSignalTrue, nil
	}

	// run pkg
	pkgContent, err := os.ReadFile(path)
	if err != nil {
		return fmt.Sprintf("failed to read file %s: %s", path, err.Error()), glob.SysSignalSystemError, err
	}

	msg, signal, newEnv, err := RunSourceCode(builtinEnv, string(pkgContent))
	if err != nil || signal != glob.SysSignalTrue {
		return msg, signal, err
	}

	pkgMgr.pkgEnv[path] = newEnv

	return msg, signal, err
}
