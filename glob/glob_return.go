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

import (
	"fmt"
	"strings"
)

type GlobRet interface {
	globRet()
	IsTrue() bool
	IsUnknown() bool
	IsErr() bool
	String() string
	ToBoolErr() (bool, error)
	IsNotTrue() bool
	IsNotUnknown() bool
	IsNotErr() bool
	Inherit(globRet GlobRet)
	Error() error
	GetREPLMsg() string
	GetMsgs() []string
}

type GlobTrue struct {
	Msg []string
}

type GlobUnknown struct {
	Msg []string
}

type GlobErr struct {
	Msg []string
}

func (v *GlobTrue) globRet()                    {}
func (v *GlobTrue) IsTrue() bool                { return true }
func (v *GlobTrue) IsUnknown() bool             { return false }
func (v *GlobTrue) IsErr() bool                 { return false }
func (v *GlobTrue) String() string              { return strings.Join(v.Msg, "\n") }
func (v *GlobTrue) ToBoolErr() (bool, error)    { return true, nil }
func (v *GlobTrue) IsNotTrue() bool             { return false }
func (v *GlobTrue) IsNotUnknown() bool          { return true }
func (v *GlobTrue) IsNotErr() bool              { return true }
func (v *GlobErr) globRet()                     {}
func (v *GlobErr) IsTrue() bool                 { return false }
func (v *GlobErr) IsUnknown() bool              { return false }
func (v *GlobErr) IsErr() bool                  { return true }
func (v *GlobErr) String() string               { return strings.Join(v.Msg, "\n") }
func (v *GlobErr) ToBoolErr() (bool, error)     { return false, fmt.Errorf(v.String()) }
func (v *GlobErr) IsNotTrue() bool              { return true }
func (v *GlobErr) IsNotUnknown() bool           { return true }
func (v *GlobErr) IsNotErr() bool               { return false }
func (v *GlobUnknown) globRet()                 {}
func (v *GlobUnknown) IsTrue() bool             { return false }
func (v *GlobUnknown) IsUnknown() bool          { return true }
func (v *GlobUnknown) IsErr() bool              { return false }
func (v *GlobUnknown) String() string           { return strings.Join(v.Msg, "\n") }
func (v *GlobUnknown) ToBoolErr() (bool, error) { return false, nil }
func (v *GlobUnknown) IsNotTrue() bool          { return true }
func (v *GlobUnknown) IsNotUnknown() bool       { return false }
func (v *GlobUnknown) IsNotErr() bool           { return true }

func NewGlobErr(s string) *GlobErr {
	if s != "" {
		return &GlobErr{Msg: []string{s}}
	}
	return &GlobErr{Msg: []string{}}
}

func NewGlobErrWithErr(err error) *GlobErr {
	return &GlobErr{Msg: []string{err.Error()}}
}

func BoolErrToGlobRet(ok bool, err error) GlobRet {
	if err != nil {
		return NewGlobErrWithMsgs([]string{err.Error()})
	}
	if ok {
		return NewGlobTrueWithMsgs([]string{})
	}
	return NewGlobUnknownWithMsgs([]string{})
}

func NewGlobTrue(s string) GlobRet {
	if s != "" {
		return &GlobTrue{Msg: []string{s}}
	}
	return &GlobTrue{Msg: []string{}}
}

func NewGlobUnknown(s string) GlobRet {
	if s != "" {
		return &GlobUnknown{Msg: []string{s}}
	}
	return &GlobUnknown{Msg: []string{}}
}

func NewGlobTrueWithMsgs(msgs []string) GlobRet {
	return &GlobTrue{Msg: msgs}
}

func NewGlobErrWithMsgs(msgs []string) GlobRet {
	return &GlobErr{Msg: msgs}
}

func NewGlobUnknownWithMsgs(msgs []string) GlobRet {
	return &GlobUnknown{Msg: msgs}
}

func (v *GlobTrue) Inherit(globRet GlobRet) {
	v.Msg = append(v.Msg, globRet.String())
}

func (v *GlobUnknown) Inherit(globRet GlobRet) {
	v.Msg = append(v.Msg, globRet.String())
}

func (v *GlobErr) Inherit(globRet GlobRet) {
	v.Msg = append(v.Msg, globRet.String())
}

func (v *GlobTrue) Error() error {
	return nil
}

func (v *GlobUnknown) Error() error {
	return nil
}

func (v *GlobErr) Error() error {
	return fmt.Errorf(v.String())
}

func (v *GlobTrue) GetREPLMsg() string {
	return REPLSuccessMessage
}

func (v *GlobUnknown) GetREPLMsg() string {
	return REPLUnknownMessage
}

func (v *GlobErr) GetREPLMsg() string {
	return REPLFailedMessage
}

func (v *GlobTrue) GetMsgs() []string {
	return v.Msg
}

func (v *GlobUnknown) GetMsgs() []string {
	return v.Msg
}

func (v *GlobErr) GetMsgs() []string {
	return v.Msg
}
