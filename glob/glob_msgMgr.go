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

type MsgMgr struct {
	Define           []string
	NewFact          []string
	VerifyProcess    []string
	Infer            []string
	System           []string
	Unknown          []string
	Error            []string
	InnerMsgMgrSlice []*MsgMgr
}

func (m *MsgMgr) String() string {
	var builder strings.Builder

	if len(m.Define) > 0 {
		builder.WriteString("by definition:\n")
		builder.WriteString(strings.Join(m.Define, "\n"))
	}

	if len(m.NewFact) > 0 {
		builder.WriteString("new fact:\n")
		builder.WriteString(strings.Join(m.NewFact, "\n"))
	}

	if len(m.VerifyProcess) > 0 {
		builder.WriteString("verify process:\n")
		builder.WriteString(strings.Join(m.VerifyProcess, "\n"))
	}

	if len(m.Infer) > 0 {
		builder.WriteString("infer:\n")
		builder.WriteString(strings.Join(m.Infer, "\n"))
	}

	if len(m.System) > 0 {
		builder.WriteString("system:\n")
		builder.WriteString(strings.Join(m.System, "\n"))
	}

	if len(m.Unknown) > 0 {
		builder.WriteString("unknown:\n")
		builder.WriteString(strings.Join(m.Unknown, "\n"))
	}

	if len(m.Error) > 0 {
		builder.WriteString("error:\n")
		builder.WriteString(strings.Join(m.Error, "\n"))
	}

	if len(m.InnerMsgMgrSlice) > 0 {
		builder.WriteString("details:\n")
		for _, innerMsgMgr := range m.InnerMsgMgrSlice {
			builder.WriteString(innerMsgMgr.String())
			builder.WriteByte('\n')
		}
	}

	return builder.String()
}

func (m *MsgMgr) AddDefine(define string) *MsgMgr {
	m.Define = append(m.Define, define)
	return m
}

func (m *MsgMgr) AddNewFact(newFact string) *MsgMgr {
	m.NewFact = append(m.NewFact, newFact)
	return m
}

func (m *MsgMgr) AddVerifyProcess(verifyProcess string) *MsgMgr {
	m.VerifyProcess = append(m.VerifyProcess, verifyProcess)
	return m
}

func (m *MsgMgr) AddInfer(infer string) *MsgMgr {
	m.Infer = append(m.Infer, infer)
	return m
}

func (m *MsgMgr) AddSystem(system string) *MsgMgr {
	m.System = append(m.System, system)
	return m
}

func (m *MsgMgr) AddUnknown(unknown string) *MsgMgr {
	m.Unknown = append(m.Unknown, unknown)
	return m
}

func (m *MsgMgr) AddError(error string) *MsgMgr {
	m.Error = append(m.Error, error)
	return m
}

func (m *MsgMgr) AddInnerMsgMgr(innerMsgMgr *MsgMgr) *MsgMgr {
	m.InnerMsgMgrSlice = append(m.InnerMsgMgrSlice, innerMsgMgr)
	return m
}

func NewEmptyMsgMgr() *MsgMgr {
	return &MsgMgr{
		Define:           []string{},
		NewFact:          []string{},
		VerifyProcess:    []string{},
		Infer:            []string{},
		System:           []string{},
		Unknown:          []string{},
		Error:            []string{},
		InnerMsgMgrSlice: []*MsgMgr{},
	}
}

func NewMsgMgrWithDefine(define string) *MsgMgr {
	ret := NewEmptyMsgMgr()
	ret.AddDefine(define)
	return ret
}

func NewMsgMgrWithNewFact(newFact string) *MsgMgr {
	ret := NewEmptyMsgMgr()
	ret.AddNewFact(newFact)
	return ret
}

func NewMsgMgrWithVerifyProcess(verifyProcess string) *MsgMgr {
	ret := NewEmptyMsgMgr()
	ret.AddVerifyProcess(verifyProcess)
	return ret
}

func NewMsgMgrWithInfer(infer string) *MsgMgr {
	ret := NewEmptyMsgMgr()
	ret.AddInfer(infer)
	return ret
}

func NewMsgMgrWithSystem(system string) *MsgMgr {
	ret := NewEmptyMsgMgr()
	ret.AddSystem(system)
	return ret
}

func NewMsgMgrWithUnknown(unknown string) *MsgMgr {
	ret := NewEmptyMsgMgr()
	ret.AddUnknown(unknown)
	return ret
}

func NewMsgMgrWithError(error string) *MsgMgr {
	ret := NewEmptyMsgMgr()
	ret.AddError(error)
	return ret
}

func NewMsgMgrWithInnerMsgMgr(innerMsgMgr *MsgMgr) *MsgMgr {
	ret := NewEmptyMsgMgr()
	ret.AddInnerMsgMgr(innerMsgMgr)
	return ret
}
