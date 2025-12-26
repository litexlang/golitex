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

type GlobRetType int8

const (
	GlobRetTypeTrue GlobRetType = iota
	GlobRetTypeUnknown
	GlobRetTypeError
)

type GlobRet struct {
	Type              GlobRetType
	Define            []string
	NewFact           []string
	VerifyProcess     []string
	Infer             []string
	System            []string
	InnerGlobRetSlice []*GlobRet
	Unknown           []string
	Error             []string
}

func (m *GlobRet) String() string {
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

	if len(m.InnerGlobRetSlice) > 0 {
		builder.WriteString("details:\n")
		for _, innerGlobRet := range m.InnerGlobRetSlice {
			builder.WriteString(innerGlobRet.String())
			builder.WriteByte('\n')
		}
	}

	return builder.String()
}

func (m *GlobRet) AddDefine(define string) *GlobRet {
	m.Define = append(m.Define, define)
	return m
}

func (m *GlobRet) AddNewFact(newFact string) *GlobRet {
	m.NewFact = append(m.NewFact, newFact)
	return m
}

func (m *GlobRet) AddVerifyProcess(verifyProcess string) *GlobRet {
	m.VerifyProcess = append(m.VerifyProcess, verifyProcess)
	return m
}

func (m *GlobRet) AddInfer(infer string) *GlobRet {
	m.Infer = append(m.Infer, infer)
	return m
}

func (m *GlobRet) AddSystem(system string) *GlobRet {
	m.System = append(m.System, system)
	return m
}

func (m *GlobRet) AddUnknown(unknown string) *GlobRet {
	m.Unknown = append(m.Unknown, unknown)
	return m
}

func (m *GlobRet) AddError(error string) *GlobRet {
	m.Error = append(m.Error, error)
	return m
}

func (m *GlobRet) AddInnerGlobRet(innerGlobRet *GlobRet) *GlobRet {
	m.InnerGlobRetSlice = append(m.InnerGlobRetSlice, innerGlobRet)
	return m
}

func NewEmptyGlobTrue() *GlobRet {
	return &GlobRet{
		Type:              GlobRetTypeTrue,
		Define:            []string{},
		NewFact:           []string{},
		VerifyProcess:     []string{},
		Infer:             []string{},
		System:            []string{},
		Unknown:           []string{},
		Error:             []string{},
		InnerGlobRetSlice: []*GlobRet{},
	}
}

func NewEmptyGlobUnknown() *GlobRet {
	return &GlobRet{
		Type:              GlobRetTypeUnknown,
		Define:            []string{},
		NewFact:           []string{},
		VerifyProcess:     []string{},
		Infer:             []string{},
		System:            []string{},
		Unknown:           []string{},
		Error:             []string{},
		InnerGlobRetSlice: []*GlobRet{},
	}
}

func NewEmptyGlobError() *GlobRet {
	return &GlobRet{
		Type:              GlobRetTypeError,
		Define:            []string{},
		NewFact:           []string{},
		VerifyProcess:     []string{},
		Infer:             []string{},
		System:            []string{},
		InnerGlobRetSlice: []*GlobRet{},
		Unknown:           []string{},
		Error:             []string{},
	}
}

func NewGlobTrueWithDefine(define string) *GlobRet {
	ret := NewEmptyGlobTrue()
	ret.AddDefine(define)
	return ret
}

func NewGlobTrueWithNewFact(newFact string) *GlobRet {
	ret := NewEmptyGlobTrue()
	ret.AddNewFact(newFact)
	return ret
}

func NewGlobTrueWithVerifyProcess(verifyProcess string) *GlobRet {
	ret := NewEmptyGlobTrue()
	ret.AddVerifyProcess(verifyProcess)
	return ret
}

func NewGlobTrueWithInfer(infer string) *GlobRet {
	ret := NewEmptyGlobTrue()
	ret.AddInfer(infer)
	return ret
}

func NewGlobTrueWithSystem(system string) *GlobRet {
	ret := NewEmptyGlobTrue()
	ret.AddSystem(system)
	return ret
}

func NewGlobTrueWithInnerGlobRet(innerGlobRet *GlobRet) *GlobRet {
	ret := NewEmptyGlobTrue()
	ret.AddInnerGlobRet(innerGlobRet)
	return ret
}

func UnknownRet(unknown string) *GlobRet {
	ret := NewEmptyGlobUnknown()
	ret.AddUnknown(unknown)
	return ret
}

func ErrRet(err error) *GlobRet {
	ret := NewEmptyGlobError()
	ret.AddError(err.Error())
	return ret
}

func (m *GlobRet) SetType(msgType GlobRetType) *GlobRet {
	m.Type = msgType
	return m
}

func (m *GlobRet) IsTrue() bool {
	return m.Type == GlobRetTypeTrue
}

func (m *GlobRet) IsUnknown() bool {
	return m.Type == GlobRetTypeUnknown
}

func (m *GlobRet) IsErr() bool {
	return m.Type == GlobRetTypeError
}

func (m *GlobRet) IsNotTrue() bool {
	return m.Type != GlobRetTypeTrue
}

func (m *GlobRet) IsNotUnknown() bool {
	return m.Type != GlobRetTypeUnknown
}

func (m *GlobRet) IsNotError() bool {
	return m.Type != GlobRetTypeError
}

func (m *GlobRet) AddREPLMsg() *GlobRet {
	switch m.Type {
	case GlobRetTypeTrue:
		m.AddSystem(REPLSuccessMessage)
	case GlobRetTypeUnknown:
		m.AddSystem(REPLUnknownMessage)
	case GlobRetTypeError:
		m.AddSystem(REPLErrorMessage)
	}
	return m
}

func (m *GlobRet) Inherit(other *GlobRet) *GlobRet {
	m.Define = append(m.Define, other.Define...)
	m.NewFact = append(m.NewFact, other.NewFact...)
	m.VerifyProcess = append(m.VerifyProcess, other.VerifyProcess...)
	m.Infer = append(m.Infer, other.Infer...)
	m.System = append(m.System, other.System...)
	m.Unknown = append(m.Unknown, other.Unknown...)
	m.Error = append(m.Error, other.Error...)
	m.InnerGlobRetSlice = append(m.InnerGlobRetSlice, other.InnerGlobRetSlice...)
	return m
}

func NewGlobTrueWithDefines(defines []string) *GlobRet {
	ret := NewEmptyGlobTrue()
	ret.Define = defines
	return ret
}

func NewGlobTrueWithNewFacts(newFacts []string) *GlobRet {
	ret := NewEmptyGlobTrue()
	ret.NewFact = newFacts
	return ret
}

func NewGlobTrueWithVerifyProcesses(verifyProcesses []string) *GlobRet {
	ret := NewEmptyGlobTrue()
	ret.VerifyProcess = verifyProcesses
	return ret
}

func NewGlobTrueWithInfers(infers []string) *GlobRet {
	ret := NewEmptyGlobTrue()
	ret.Infer = infers
	return ret
}

func NewGlobTrueWithSystems(systems []string) *GlobRet {
	ret := NewEmptyGlobTrue()
	ret.System = systems
	return ret
}

func NewGlobUnknownWithInnerGlobRets(innerGlobRets []*GlobRet) *GlobRet {
	ret := NewEmptyGlobUnknown()
	ret.InnerGlobRetSlice = innerGlobRets
	return ret
}

func NewGlobUnknownWithUnknowns(unknowns []string) *GlobRet {
	ret := NewEmptyGlobUnknown()
	ret.Unknown = unknowns
	return ret
}

func NewGlobErrorWithErrors(errors []string) *GlobRet {
	ret := NewEmptyGlobError()
	ret.Error = errors
	return ret
}
