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
	"strings"
)

type ExecRet interface {
	execRet()
	IsTrue() bool
	IsUnknown() bool
	IsErr() bool
	NewVerMsg(verState *VerState, msg string) ExecRet
	String() string
	ToBoolErr() (bool, error)
	IsNotTrue() bool
	IsNotUnknown() bool
	IsNotErr() bool
	Inherit(execRet ExecRet)
	NewVerMsgAtBegin(verState *VerState, msg string) ExecRet
}

type ExecTrue struct {
	Msg             []string
	TrueEqualValues []ast.Fc
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
func (v *ExecUnknown) ToBoolErr() (bool, error) { return false, nil }
func (v *ExecUnknown) IsNotTrue() bool          { return true }
func (v *ExecUnknown) IsNotUnknown() bool       { return false }
func (v *ExecUnknown) IsNotErr() bool           { return true }

func NewExecErr(s string) *ExecErr {
	if s != "" {
		return &ExecErr{Msg: []string{s}}
	}
	return &ExecErr{Msg: []string{}}
}

func NewExecErrWithErr(err error) *ExecErr {
	return &ExecErr{Msg: []string{err.Error()}}
}

func BoolErrToExecRet(ok bool, err error) ExecRet {
	if err != nil {
		return &ExecErr{Msg: []string{err.Error()}}
	}
	if ok {
		return &ExecTrue{Msg: []string{}}
	}
	return &ExecUnknown{Msg: []string{}}
}

func NewExecTrue(s string) ExecRet {
	if s != "" {
		return &ExecTrue{Msg: []string{s}}
	}
	return &ExecTrue{Msg: []string{}, TrueEqualValues: nil}
}

func NewExecUnknown(s string) ExecRet {
	if s != "" {
		return &ExecUnknown{Msg: []string{s}}
	}
	return &ExecUnknown{Msg: []string{}}
}

func NewExecTrueWithValues(s string, equalValue []ast.Fc) ExecRet {
	if s != "" {
		return &ExecTrue{Msg: []string{s}, TrueEqualValues: equalValue}
	}
	if len(equalValue) != 2 {
		panic("equal value length must be 2")
	}
	return &ExecTrue{Msg: []string{}, TrueEqualValues: []ast.Fc{equalValue[0], equalValue[1]}}
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
