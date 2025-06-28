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

package litex_executor

import (
	env "golitex/environment"
	glob "golitex/glob"
)

var RuntimeEnvSlice []*env.Env = []*env.Env{}

func ExecImportStmtInit(newPkg string, path string, env *env.Env) error {
	RuntimeEnvSlice = append(RuntimeEnvSlice, env)
	err := glob.ImportStmtInit(newPkg, path)
	return err
}

func ExecImportStmtEnd(env *env.Env) error {
	RuntimeEnvSlice = RuntimeEnvSlice[:len(RuntimeEnvSlice)-1]
	glob.ImportStmtEnd()
	return nil
}
