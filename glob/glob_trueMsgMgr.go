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

type TrueMsgMgr struct {
	Define        []string
	NewFact       []string
	VerifyProcess []string
	Infer         []string
	System        []string
}

func (m *TrueMsgMgr) String() string {
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

	return builder.String()
}

func (m *TrueMsgMgr) AddDefine(define string) *TrueMsgMgr {
	m.Define = append(m.Define, define)
	return m
}

func (m *TrueMsgMgr) AddNewFact(newFact string) *TrueMsgMgr {
	m.NewFact = append(m.NewFact, newFact)
	return m
}

func (m *TrueMsgMgr) AddVerifyProcess(verifyProcess string) *TrueMsgMgr {
	m.VerifyProcess = append(m.VerifyProcess, verifyProcess)
	return m
}

func (m *TrueMsgMgr) AddInfer(infer string) *TrueMsgMgr {
	m.Infer = append(m.Infer, infer)
	return m
}

func (m *TrueMsgMgr) AddSystem(system string) *TrueMsgMgr {
	m.System = append(m.System, system)
	return m
}

func NewEmptyTrueMsgMgr() *TrueMsgMgr {
	return &TrueMsgMgr{
		Define:        []string{},
		NewFact:       []string{},
		VerifyProcess: []string{},
		Infer:         []string{},
		System:        []string{},
	}
}

func NewTrueMsgWithDefine(define string) *TrueMsgMgr {
	ret := NewEmptyTrueMsgMgr()
	ret.AddDefine(define)
	return ret
}

func NewTrueMsgWithNewFact(newFact string) *TrueMsgMgr {
	ret := NewEmptyTrueMsgMgr()
	ret.AddNewFact(newFact)
	return ret
}

func NewTrueMsgWithVerifyProcess(verifyProcess string) *TrueMsgMgr {
	ret := NewEmptyTrueMsgMgr()
	ret.AddVerifyProcess(verifyProcess)
	return ret
}

func NewTrueMsgWithInfer(infer string) *TrueMsgMgr {
	ret := NewEmptyTrueMsgMgr()
	ret.AddInfer(infer)
	return ret
}

func NewTrueMsgWithSystem(system string) *TrueMsgMgr {
	ret := NewEmptyTrueMsgMgr()
	ret.AddSystem(system)
	return ret
}
