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
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

// type Executor env.Env

type Executor struct {
	env *env.Env
}

func NewExecutor(curEnv *env.Env) *Executor {
	if curEnv == nil {
		return &Executor{env: env.NewEnv(nil, nil)}
	} else {
		return &Executor{env: curEnv}
	}
}

func (e *Executor) newEnv(parent *env.Env, curMatchEnv *ast.SpecFactStmt) *env.Env {
	e.env = env.NewEnv(parent, curMatchEnv)
	return e.env
}

func (e *Executor) deleteEnvAndRetainMsg() {
	for _, msg := range e.env.Msgs {
		e.env.Parent.NewMsg(msg)
	}
	e.env = e.env.Parent
}

func (e *Executor) appendMsg(msg string, str ...any) {
	e.env.Msgs = append(e.env.Msgs, fmt.Sprintf(msg, str...))
}

func (e *Executor) appendNewMsgAtBegin(msg string, str ...any) {
	e.env.Msgs = append([]string{fmt.Sprintf(msg, str...)}, e.env.Msgs...)
}

func (e *Executor) appendWarningMsg(msg string, str ...any) {
	e.env.Msgs = append(e.env.Msgs, fmt.Sprintf(`warning: %s`, fmt.Sprintf(msg, str...)))
}

func (e *Executor) appendInternalWarningMsg(msg string, str ...any) {
	e.env.Msgs = append(e.env.Msgs, glob.InternalWarningMsg(msg, str...))
}
