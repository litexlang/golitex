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
	ast "golitex/ast"
	env "golitex/environment"
)

// type Executor env.Env

type Executor struct {
	env *env.Env
}

func NewExecutor(curEnv *env.Env, isSandBoxUpperBound bool) *Executor {
	if curEnv == nil {
		return &Executor{env: env.NewEnv(nil, nil, isSandBoxUpperBound)}
	} else {
		return &Executor{env: curEnv}
	}
}

func (e *Executor) newEnv(parent *env.Env, curMatchEnv *ast.SpecFactStmt, isSandBoxUpperBound bool) *env.Env {
	e.env = env.NewEnv(parent, curMatchEnv, isSandBoxUpperBound)
	return e.env
}
