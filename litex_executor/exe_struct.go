// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_executor

import (
	"fmt"
	env "golitex/litex_env"
)

// type Executor env.Env

type Executor struct {
	env    *env.Env
	curPkg string // 在多pkg模式下才有用。并行地执行玩引用的包里的东西后，合并所有的环境的时候，把那个环境里的 pkgName = "" 的东西，全部替换成当前 curPkg 下面的东西
}

// 如果你传入的是nil，那默认这个exec里的env的curPkg是""
func NewExecutor(curEnv *env.Env) *Executor {
	if curEnv == nil {
		return &Executor{env: env.NewEnv(nil)}
	} else {
		return &Executor{env: curEnv}
	}
}

func (e *Executor) newEnv() {
	e.env = env.NewEnv(e.env)
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

func (e *Executor) appendNewMsgAtBegin(msg string, str ...any) {
	e.env.Msgs = append([]string{fmt.Sprintf(msg, str...)}, e.env.Msgs...)
}

func (e *Executor) appendWarningMsg(msg string, str ...any) {
	e.env.Msgs = append(e.env.Msgs, fmt.Sprintf(`warning: %s`, fmt.Sprintf(msg, str...)))
}
