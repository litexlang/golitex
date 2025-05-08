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

package litex_global

type ExecState uint8

const (
	ExecState_Unknown ExecState = iota
	ExecState_True
	ExecState_Error
	ExecState_False
)

func (e *ExecState) IsTrue() ExecState {
	return ExecState_True
}

func (e *ExecState) IsUnknown() ExecState {
	return ExecState_Unknown
}

func (e *ExecState) IsError() ExecState {
	return ExecState_Error
}

func (e *ExecState) IsFalse() ExecState {
	return ExecState_False
}
