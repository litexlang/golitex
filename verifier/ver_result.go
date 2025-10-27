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

package litex_verifier

import (
	"fmt"
	"strings"
)

type VerRet interface {
	verRet()
	IsTrue() bool
	IsUnknown() bool
	IsErr() bool
	AddMsg(msg string)
	String() string
	ToBoolErr() (bool, error)
}

type VerTrue struct {
	Msg []string
}

type VerUnknown struct {
	Msg []string
}

type VerErr struct {
	Msg []string
}

func (v *VerTrue) verRet()                     {}
func (v *VerTrue) IsTrue() bool                { return true }
func (v *VerTrue) IsUnknown() bool             { return false }
func (v *VerTrue) IsErr() bool                 { return false }
func (v *VerTrue) AddMsg(msg string)           { v.Msg = append(v.Msg, msg) }
func (v *VerTrue) String() string              { return strings.Join(v.Msg, "\n") }
func (v *VerTrue) ToBoolErr() (bool, error)    { return true, nil }
func (v *VerErr) verRet()                      {}
func (v *VerErr) IsTrue() bool                 { return false }
func (v *VerErr) IsUnknown() bool              { return false }
func (v *VerErr) IsErr() bool                  { return true }
func (v *VerErr) AddMsg(msg string)            { v.Msg = append(v.Msg, msg) }
func (v *VerErr) String() string               { return strings.Join(v.Msg, "\n") }
func (v *VerErr) ToBoolErr() (bool, error)     { return false, fmt.Errorf(v.String()) }
func (v *VerUnknown) verRet()                  {}
func (v *VerUnknown) IsTrue() bool             { return false }
func (v *VerUnknown) IsUnknown() bool          { return true }
func (v *VerUnknown) IsErr() bool              { return false }
func (v *VerUnknown) AddMsg(msg string)        { v.Msg = append(v.Msg, msg) }
func (v *VerUnknown) String() string           { return strings.Join(v.Msg, "\n") }
func (v *VerUnknown) ToBoolErr() (bool, error) { return false, nil }

func newVerErr(s string) *VerErr {
	if s != "" {
		return &VerErr{Msg: []string{s}}
	}
	return &VerErr{Msg: []string{}}
}

func BoolErrToVerRet(ok bool, err error) VerRet {
	if err != nil {
		return &VerErr{Msg: []string{err.Error()}}
	}
	if ok {
		return &VerTrue{Msg: []string{}}
	}
	return &VerUnknown{Msg: []string{}}
}

func NewTrueVerRet(s string) VerRet {
	if s != "" {
		return &VerTrue{Msg: []string{s}}
	}
	return &VerTrue{Msg: []string{}}
}

func NewUnknownVerRet(s string) VerRet {
	if s != "" {
		return &VerUnknown{Msg: []string{s}}
	}
	return &VerUnknown{Msg: []string{}}
}
