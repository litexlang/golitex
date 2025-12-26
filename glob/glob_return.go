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

import (
	"fmt"
	"regexp"
	"strings"
)

var newlineRegex = regexp.MustCompile(`\n{3,}`)

type GlobRet interface {
	globRet()
	IsTrue() bool
	IsUnknown() bool
	IsErr() bool
	String() string
	IsNotTrue() bool
	IsNotUnknown() bool
	IsNotErr() bool
	GetMsgs() []string
	StringWithOptimizedNewline() string
	AddMsg(msg string) GlobRet
	AddNewREPLMsg() GlobRet
	AddMsgs(msgs []string) GlobRet
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

func (v *GlobTrue) globRet()              {}
func (v *GlobTrue) IsTrue() bool          { return true }
func (v *GlobTrue) IsUnknown() bool       { return false }
func (v *GlobTrue) IsErr() bool           { return false }
func (v *GlobTrue) String() string        { return strings.Join(v.Msg, "\n") }
func (v *GlobTrue) IsNotTrue() bool       { return false }
func (v *GlobTrue) IsNotUnknown() bool    { return true }
func (v *GlobTrue) IsNotErr() bool        { return true }
func (v *GlobErr) globRet()               {}
func (v *GlobErr) IsTrue() bool           { return false }
func (v *GlobErr) IsUnknown() bool        { return false }
func (v *GlobErr) IsErr() bool            { return true }
func (v *GlobErr) String() string         { return strings.Join(v.Msg, "\n") }
func (v *GlobErr) IsNotTrue() bool        { return true }
func (v *GlobErr) IsNotUnknown() bool     { return true }
func (v *GlobErr) IsNotErr() bool         { return false }
func (v *GlobUnknown) globRet()           {}
func (v *GlobUnknown) IsTrue() bool       { return false }
func (v *GlobUnknown) IsUnknown() bool    { return true }
func (v *GlobUnknown) IsErr() bool        { return false }
func (v *GlobUnknown) String() string     { return strings.Join(v.Msg, "\n") }
func (v *GlobUnknown) IsNotTrue() bool    { return true }
func (v *GlobUnknown) IsNotUnknown() bool { return false }
func (v *GlobUnknown) IsNotErr() bool     { return true }

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

// ErrRet returns a GlobErr with the given error message. If err is nil, returns empty error message.
func ErrRet(err error) GlobRet {
	if err != nil {
		return NewGlobErr(err.Error())
	}
	return NewEmptyGlobErr()
}

func (v *GlobTrue) GetREPLMsg() string {
	return REPLSuccessMessage
}

func (v *GlobUnknown) GetREPLMsg() string {
	return REPLUnknownMessage
}

func (v *GlobErr) GetREPLMsg() string {
	return REPLErrorMessage
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

func (v *GlobTrue) StringWithOptimizedNewline() string {
	// 把末尾的空
	s := strings.Trim(v.String(), "\n\t ")
	// 将3个或更多连续的\n替换成\n\n
	s = newlineRegex.ReplaceAllString(s, "\n\n")
	return fmt.Sprintf("%s\n", s)
}

func (v *GlobUnknown) StringWithOptimizedNewline() string {
	s := strings.Trim(v.String(), "\n\t ")
	// 将3个或更多连续的\n替换成\n\n
	s = newlineRegex.ReplaceAllString(s, "\n\n")
	return fmt.Sprintf("%s\n", s)
}

func (v *GlobErr) StringWithOptimizedNewline() string {
	s := strings.Trim(v.String(), "\n\t ")
	// 将3个或更多连续的\n替换成\n\n
	s = newlineRegex.ReplaceAllString(s, "\n\n")
	return fmt.Sprintf("%s\n", s)
}

func (v *GlobTrue) AddMsg(msg string) GlobRet {
	v.Msg = append(v.Msg, msg)
	return v
}

func (v *GlobUnknown) AddMsg(msg string) GlobRet {
	v.Msg = append(v.Msg, msg)
	return v
}

func (v *GlobErr) AddMsg(msg string) GlobRet {
	v.Msg = append(v.Msg, msg)
	return v
}

func NewEmptyGlobTrue() GlobRet {
	return NewGlobTrueWithMsgs([]string{})
}

func NewEmptyGlobUnknown() GlobRet {
	return NewGlobUnknownWithMsgs([]string{})
}

func NewEmptyGlobErr() GlobRet {
	return NewGlobErrWithMsgs([]string{})
}

func (v *GlobTrue) AddNewREPLMsg() GlobRet {
	v.Msg = append(v.Msg, REPLSuccessMessage)
	return v
}

func (v *GlobUnknown) AddNewREPLMsg() GlobRet {
	v.Msg = append(v.Msg, REPLUnknownMessage)
	return v
}

func (v *GlobErr) AddNewREPLMsg() GlobRet {
	v.Msg = append(v.Msg, REPLErrorMessage)
	return v
}

func (v *GlobTrue) AddMsgs(msgs []string) GlobRet {
	v.Msg = append(v.Msg, msgs...)
	return v
}

func (v *GlobUnknown) AddMsgs(msgs []string) GlobRet {
	v.Msg = append(v.Msg, msgs...)
	return v
}

func (v *GlobErr) AddMsgs(msgs []string) GlobRet {
	v.Msg = append(v.Msg, msgs...)
	return v
}
