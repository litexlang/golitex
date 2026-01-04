// Copyright Jiachen Shen.
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

import "strings"

type ShortRet struct {
	RetType StmtRetType
	Msgs    []string
}

func NewShortRet(retType StmtRetType, msgs []string) *ShortRet {
	return &ShortRet{
		RetType: retType,
		Msgs:    msgs,
	}
}

func (sr *ShortRet) IsTrue() bool {
	return sr.RetType == StmtRetTypeTrue
}

func (sr *ShortRet) IsUnknown() bool {
	return sr.RetType == StmtRetTypeUnknown
}

func (sr *ShortRet) IsErr() bool {
	return sr.RetType == StmtRetTypeError
}

func (sr *ShortRet) SetType(retType StmtRetType) *ShortRet {
	sr.RetType = retType
	return sr
}

func ErrStmtMsgToShortRet(stmtRet *StmtRet) *ShortRet {
	return NewShortRet(stmtRet.RetType, stmtRet.Error)
}

func NewEmptyShortUnknownRet() *ShortRet {
	return NewShortRet(StmtRetTypeUnknown, []string{})
}

func NewEmptyShortErrorRet() *ShortRet {
	return NewShortRet(StmtRetTypeError, []string{})
}

func NewEmptyShortTrueRet() *ShortRet {
	return NewShortRet(StmtRetTypeTrue, []string{})
}

func NewShortRetTrue(s string) *ShortRet {
	ret := NewEmptyShortTrueRet()
	ret.Msgs = append(ret.Msgs, s)
	return ret
}

func NewShortRetErr(s string) *ShortRet {
	ret := NewEmptyShortErrorRet()
	ret.Msgs = append(ret.Msgs, s)
	return ret
}

func (sr *ShortRet) String() string {
	return strings.Join(sr.Msgs, "\n")
}

func (sr *ShortRet) IsNotTrue() bool {
	return sr.RetType != StmtRetTypeTrue
}
