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

package litex_ast

import "strings"

type ShortRet interface {
	shortRet()
	IsTrue() bool
	IsUnknown() bool
	IsErr() bool
	IsNotTrue() bool
	String() string
	GetMsg() []string
	ToEmptyVerREt() VerRet
	AddExtraInfo(extraInfo string) ShortRet
}

type TrueShortRet struct {
	Msg []string
}

type UnknownShortRet struct {
	Msg []string
}

type ErrShortRet struct {
	Msg []string
}

func (r *TrueShortRet) shortRet()       {}
func (r *TrueShortRet) IsTrue() bool    { return true }
func (r *TrueShortRet) IsUnknown() bool { return false }
func (r *TrueShortRet) IsErr() bool     { return false }
func (r *TrueShortRet) IsNotTrue() bool { return false }

func (r *UnknownShortRet) shortRet()       {}
func (r *UnknownShortRet) IsTrue() bool    { return false }
func (r *UnknownShortRet) IsUnknown() bool { return true }
func (r *UnknownShortRet) IsErr() bool     { return false }
func (r *UnknownShortRet) IsNotTrue() bool { return true }
func (r *ErrShortRet) shortRet()           {}
func (r *ErrShortRet) IsTrue() bool        { return false }
func (r *ErrShortRet) IsUnknown() bool     { return false }
func (r *ErrShortRet) IsErr() bool         { return true }
func (r *ErrShortRet) IsNotTrue() bool     { return true }

func NewTrueShortRet() ShortRet {
	return &TrueShortRet{Msg: []string{}}
}

func NewUnknownShortRet() ShortRet {
	return &UnknownShortRet{Msg: []string{}}
}

func NewErrShortRet() ShortRet {
	return &ErrShortRet{Msg: []string{}}
}

func NewTrueShortRetWithMsg(msg string) ShortRet {
	return &TrueShortRet{Msg: []string{msg}}
}

func NewUnknownShortRetWithMsg(msg string) ShortRet {
	return &UnknownShortRet{Msg: []string{msg}}
}

func NewErrShortRetWithMsg(msg string) ShortRet {
	return &ErrShortRet{Msg: []string{msg}}
}

func (r *TrueShortRet) String() string {
	return strings.Join(r.Msg, "\n")
}

func (r *UnknownShortRet) String() string {
	return strings.Join(r.Msg, "\n")
}

func (r *ErrShortRet) String() string {
	return strings.Join(r.Msg, "\n")
}

func (r *TrueShortRet) GetMsg() []string {
	return r.Msg
}

func (r *UnknownShortRet) GetMsg() []string {
	return r.Msg
}

func (r *ErrShortRet) GetMsg() []string {
	return r.Msg
}

func (r *TrueShortRet) ToEmptyVerREt() VerRet {
	return NewTrueVerRet(nil, nil, r.String())
}

func (r *ErrShortRet) ToEmptyVerREt() VerRet {
	return NewErrVerRet(nil).AddExtraInfo(r.String())
}

func (r *UnknownShortRet) ToEmptyVerREt() VerRet {
	return NewUnknownVerRet(nil).AddExtraInfo(r.String())
}

func (r *TrueShortRet) AddExtraInfo(extraInfo string) ShortRet {
	r.Msg = append(r.Msg, extraInfo)
	return r
}

func (r *UnknownShortRet) AddExtraInfo(extraInfo string) ShortRet {
	r.Msg = append(r.Msg, extraInfo)
	return r
}

func (r *ErrShortRet) AddExtraInfo(extraInfo string) ShortRet {
	r.Msg = append(r.Msg, extraInfo)
	return r
}
