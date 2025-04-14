// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_executor

import (
	"fmt"
	env "golitex/litex_env"
)

// type Executor env.Env

type Executor struct {
	env *env.Env
}

// 如果你传入的是nil，那默认这个exec里的env的curPkg是""
func NewExecutor(curEnv *env.Env) *Executor {
	if curEnv == nil {
		return &Executor{env: env.NewEnv(nil, nil, "")}
	} else {
		return &Executor{env: curEnv}
	}
}

func (e *Executor) newEnv(curPkg string) {
	e.env = env.NewEnv(e.env, nil, curPkg)
}

func (e *Executor) deleteEnvAndRetainMsg() {
	for _, msg := range e.env.Msgs {
		e.env.Parent.NewMsg(msg)
	}
	e.env = e.env.Parent
}

func (e *Executor) clearMsgAndOutput() {
	e.env.Msgs = []string{}
}

func (e *Executor) appendNewMsg(msg string, str ...any) {
	e.env.Msgs = append(e.env.Msgs, fmt.Sprintf(msg, str...))
}
