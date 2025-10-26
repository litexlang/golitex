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

package litex_global

type ExecState uint8

const (
	ExecStateUnknown ExecState = iota
	ExecStateTrue
	ExecStateError
)

type ExecRet interface {
	execRet()
	IsTrue() bool
	IsUnknown() bool
	IsError() bool
	AddMsg(msg string)
	String() string
}

type ExecTrue struct {
	Msg []string
}

type ExecUnknown struct {
	Msg []string
}

type ExecErr struct {
	Msg []string
}
