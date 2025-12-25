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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strings"
)

type ExecRet interface {
	execRet()
	IsTrue() bool
	IsUnknown() bool
	IsErr() bool
	NewVerMsg(verState *VerState, msg string) ExecRet
	String() string
	GetMsgs() []string
	ToBoolErr() (bool, error)
	IsNotTrue() bool
	IsNotUnknown() bool
	IsNotErr() bool
	Inherit(execRet ExecRet)
	NewVerMsgAtBegin(verState *VerState, msg string) ExecRet
	ToGlobRet() glob.GlobRet
	AddMsg(msg string) ExecRet
	AddMsgAtBegin(msg string) ExecRet
	AddMsgs(msgs []string) ExecRet
	AddNewLineAndMsg(msg string) ExecRet
}

type ExecTrue struct {
	Msg             []string
	TrueEqualValues []ast.Obj
}

type ExecUnknown struct {
	Msg []string
}

type ExecErr struct {
	Msg []string
}

func (v *ExecTrue) execRet()        {}
func (v *ExecTrue) IsTrue() bool    { return true }
func (v *ExecTrue) IsUnknown() bool { return false }
func (v *ExecTrue) IsErr() bool     { return false }
func (v *ExecTrue) NewVerMsg(verState *VerState, msg string) ExecRet {
	if verState.IsWithMsg() {
		v.Msg = append(v.Msg, msg)
	}
	return v
}
func (v *ExecTrue) String() string           { return strings.Join(v.Msg, "\n") }
func (v *ExecTrue) GetMsgs() []string        { return v.Msg }
func (v *ExecTrue) ToBoolErr() (bool, error) { return true, nil }
func (v *ExecTrue) IsNotTrue() bool          { return false }
func (v *ExecTrue) IsNotUnknown() bool       { return true }
func (v *ExecTrue) IsNotErr() bool           { return true }
func (v *ExecErr) execRet()                  {}
func (v *ExecErr) IsTrue() bool              { return false }
func (v *ExecErr) IsUnknown() bool           { return false }
func (v *ExecErr) IsErr() bool               { return true }
func (v *ExecErr) NewVerMsg(verState *VerState, msg string) ExecRet {
	if verState.IsWithMsg() {
		v.Msg = append(v.Msg, msg)
	}
	return v
}
func (v *ExecErr) String() string           { return strings.Join(v.Msg, "\n") }
func (v *ExecErr) GetMsgs() []string        { return v.Msg }
func (v *ExecErr) ToBoolErr() (bool, error) { return false, fmt.Errorf(v.String()) }
func (v *ExecErr) IsNotTrue() bool          { return true }
func (v *ExecErr) IsNotUnknown() bool       { return true }
func (v *ExecErr) IsNotErr() bool           { return false }
func (v *ExecUnknown) execRet()             {}
func (v *ExecUnknown) IsTrue() bool         { return false }
func (v *ExecUnknown) IsUnknown() bool      { return true }
func (v *ExecUnknown) IsErr() bool          { return false }
func (v *ExecUnknown) NewVerMsg(verState *VerState, msg string) ExecRet {
	if verState.IsWithMsg() {
		v.Msg = append(v.Msg, msg)
	}
	return v
}
func (v *ExecUnknown) String() string           { return strings.Join(v.Msg, "\n") }
func (v *ExecUnknown) GetMsgs() []string        { return v.Msg }
func (v *ExecUnknown) ToBoolErr() (bool, error) { return false, nil }
func (v *ExecUnknown) IsNotTrue() bool          { return true }
func (v *ExecUnknown) IsNotUnknown() bool       { return false }
func (v *ExecUnknown) IsNotErr() bool           { return true }

func NewExecErr(s string) *ExecErr {
	return &ExecErr{Msg: []string{s}}
}

func NewExecErrWithErr(err error) *ExecErr {
	return &ExecErr{Msg: []string{err.Error()}}
}

func BoolErrToExecRet(ok bool, err error) ExecRet {
	if err != nil {
		return NewExecErrWithMsgs([]string{err.Error()})
	}
	if ok {
		return NewExecTrueWithMsgs([]string{})
	}
	return NewExecUnknownWithMsgs([]string{})
}

func NewExecTrue(s string) ExecRet {
	return &ExecTrue{Msg: []string{s}, TrueEqualValues: nil}
}

func NewEmptyExecUnknown() ExecRet {
	return &ExecUnknown{Msg: []string{}}
}

func NewEmptyExecErr() ExecRet {
	return &ExecErr{Msg: []string{}}
}

func NewEmptyExecTrue() ExecRet {
	return &ExecTrue{Msg: []string{}}
}

func NewExecUnknown(s string) ExecRet {
	return &ExecUnknown{Msg: []string{s}}
}

func NewExecTrueWithValues(s string, equalValue []ast.Obj) ExecRet {
	if s != "" {
		return &ExecTrue{Msg: []string{s}, TrueEqualValues: equalValue}
	}
	if len(equalValue) != 2 {
		panic("equal value length must be 2")
	}
	return &ExecTrue{Msg: []string{}, TrueEqualValues: []ast.Obj{equalValue[0], equalValue[1]}}
}

func NewExecTrueWithMsgs(msgs []string) ExecRet {
	return &ExecTrue{Msg: msgs}
}

func NewExecErrWithMsgs(msgs []string) ExecRet {
	return &ExecErr{Msg: msgs}
}

func NewExecUnknownWithMsgs(msgs []string) ExecRet {
	return &ExecUnknown{Msg: msgs}
}

func (v *ExecTrue) Inherit(execRet ExecRet) {
	v.Msg = append(v.Msg, execRet.String())
}

func (v *ExecUnknown) Inherit(execRet ExecRet) {
	v.Msg = append(v.Msg, execRet.String())
}

func (v *ExecErr) Inherit(execRet ExecRet) {
	v.Msg = append(v.Msg, execRet.String())
}

func (v *ExecTrue) NewVerMsgAtBegin(verState *VerState, msg string) ExecRet {
	if verState.IsWithMsg() {
		v.Msg = append([]string{msg}, v.Msg...)
	}
	return v
}

func (v *ExecUnknown) NewVerMsgAtBegin(verState *VerState, msg string) ExecRet {
	if verState.IsWithMsg() {
		v.Msg = append([]string{msg}, v.Msg...)
	}
	return v
}

func (v *ExecErr) NewVerMsgAtBegin(verState *VerState, msg string) ExecRet {
	if verState.IsWithMsg() {
		v.Msg = append([]string{msg}, v.Msg...)
	}
	return v
}

func (v *ExecTrue) NewVerMsgAtEnd(verState *VerState, msg string) ExecRet {
	if verState.IsWithMsg() {
		v.Msg = append(v.Msg, msg)
	}
	return v
}

func (v *ExecUnknown) NewVerMsgAtEnd(verState *VerState, msg string) ExecRet {
	if verState.IsWithMsg() {
		v.Msg = append(v.Msg, msg)
	}
	return v
}

func (v *ExecTrue) ToGlobRet() glob.GlobRet {
	msgs := v.GetMsgs()
	return glob.NewGlobTrueWithMsgs(msgs)
}

func (v *ExecUnknown) ToGlobRet() glob.GlobRet {
	msgs := v.GetMsgs()
	return glob.NewGlobUnknownWithMsgs(msgs)
}

func (v *ExecErr) ToGlobRet() glob.GlobRet {
	msgs := v.GetMsgs()
	return glob.NewGlobErrWithMsgs(msgs)
}

func (v *ExecTrue) AddMsg(msg string) ExecRet {
	v.Msg = append(v.Msg, msg)
	return v
}

func (v *ExecUnknown) AddMsg(msg string) ExecRet {
	v.Msg = append(v.Msg, msg)
	return v
}

func (v *ExecErr) AddMsg(msg string) ExecRet {
	v.Msg = append(v.Msg, msg)
	return v
}

func (v *ExecTrue) AddMsgAtBegin(msg string) ExecRet {
	v.Msg = append([]string{msg}, v.Msg...)
	return v
}

func (v *ExecUnknown) AddMsgAtBegin(msg string) ExecRet {
	v.Msg = append([]string{msg}, v.Msg...)
	return v
}

func (v *ExecErr) AddMsgAtBegin(msg string) ExecRet {
	v.Msg = append([]string{msg}, v.Msg...)
	return v
}

func (v *ExecTrue) AddMsgs(msgs []string) ExecRet {
	v.Msg = append(v.Msg, msgs...)
	return v
}

func (v *ExecUnknown) AddMsgs(msgs []string) ExecRet {
	v.Msg = append(v.Msg, msgs...)
	return v
}

func (v *ExecErr) AddMsgs(msgs []string) ExecRet {
	v.Msg = append(v.Msg, msgs...)
	return v
}

func (v *ExecTrue) AddNewLineAndMsg(msg string) ExecRet {
	v.Msg = append(v.Msg, "\n", msg)
	return v
}

func (v *ExecUnknown) AddNewLineAndMsg(msg string) ExecRet {
	v.Msg = append(v.Msg, "\n", msg)
	return v
}

func (v *ExecErr) AddNewLineAndMsg(msg string) ExecRet {
	v.Msg = append(v.Msg, "\n", msg)
	return v
}
