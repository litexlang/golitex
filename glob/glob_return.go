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
	"strings"
)

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
	Stmt              []string
	InnerGlobRetSlice []*GlobRet
	Unknown           []string
	Error             []string
	Warnings          []string

	Line uint
}

func (m *GlobRet) String() string {
	var builder strings.Builder

	builder.WriteString(fmt.Sprintf("--- line %d ---\n\n", m.Line))

	if len(m.Stmt) > 0 {
		builder.WriteString("statement:\n")
		builder.WriteString(strings.Join(m.Stmt, "\n"))
		builder.WriteString("\n\n")
	}

	if len(m.Define) > 0 {
		builder.WriteString("by definition:\n")
		builder.WriteString(strings.Join(m.Define, "\n"))
		builder.WriteString("\n\n")
	}

	if len(m.NewFact) > 0 {
		builder.WriteString("new fact:\n")
		builder.WriteString(strings.Join(m.NewFact, "\n"))
		builder.WriteString("\n\n")
	}

	if len(m.VerifyProcess) > 0 {
		builder.WriteString("verify process:\n")
		builder.WriteString(strings.Join(m.VerifyProcess, "\n"))
		builder.WriteString("\n\n")
	}

	if len(m.Infer) > 0 {
		builder.WriteString("infer:\n")
		builder.WriteString(strings.Join(m.Infer, "\n"))
		builder.WriteString("\n\n")
	}

	if len(m.Unknown) > 0 {
		builder.WriteString("unable to verify:\n")
		builder.WriteString(strings.Join(m.Unknown, "\n"))
		builder.WriteString("\n\n")
	}

	if len(m.Error) > 0 {
		builder.WriteString("error:\n")
		builder.WriteString(strings.Join(m.Error, "\n"))
		builder.WriteString("\n\n")
	}

	if len(m.InnerGlobRetSlice) > 0 {
		builder.WriteString("details:\n")
		for _, innerGlobRet := range m.InnerGlobRetSlice {
			builder.WriteString(innerGlobRet.String())
			builder.WriteString("\n\n")
		}
		builder.WriteString("\n\n")
	}

	if len(m.Warnings) > 0 {
		builder.WriteString("warning:\n")
		builder.WriteString(strings.Join(m.Warnings, "\n"))
		builder.WriteString("\n\n")
	}

	return builder.String()
}

func (m *GlobRet) AddDefine(define string) *GlobRet {
	if define == "" {
		return m
	}
	m.Define = append(m.Define, define)
	return m
}

func (m *GlobRet) AddNewFact(newFact string) *GlobRet {
	if newFact == "" {
		return m
	}
	m.NewFact = append(m.NewFact, newFact)
	return m
}

func (m *GlobRet) AddVerifyProcess(verifyProcess string) *GlobRet {
	if verifyProcess == "" {
		return m
	}
	m.VerifyProcess = append(m.VerifyProcess, verifyProcess)
	return m
}

func (m *GlobRet) AddInfer(infer string) *GlobRet {
	if infer == "" {
		return m
	}
	m.Infer = append(m.Infer, infer)
	return m
}

func (m *GlobRet) AddStmt(s string) *GlobRet {
	if s == "" {
		return m
	}
	m.Stmt = append(m.Stmt, s)
	return m
}

func (m *GlobRet) AddUnknown(unknown string) *GlobRet {
	if unknown == "" {
		return m
	}
	m.Unknown = append(m.Unknown, unknown)
	return m
}

func (m *GlobRet) AddError(error string) *GlobRet {
	if error == "" {
		return m
	}
	m.Error = append(m.Error, error)
	return m
}

func (m *GlobRet) AddInnerGlobRet(innerGlobRet *GlobRet) *GlobRet {
	if innerGlobRet == nil {
		return m
	}
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
		Stmt:              []string{},
		Unknown:           []string{},
		Error:             []string{},
		InnerGlobRetSlice: []*GlobRet{},
		Warnings:          []string{},
		Line:              0,
	}
}

func NewEmptyGlobUnknown() *GlobRet {
	return &GlobRet{
		Type:              GlobRetTypeUnknown,
		Define:            []string{},
		NewFact:           []string{},
		VerifyProcess:     []string{},
		Infer:             []string{},
		Stmt:              []string{},
		Unknown:           []string{},
		Error:             []string{},
		InnerGlobRetSlice: []*GlobRet{},
		Warnings:          []string{},
		Line:              0,
	}
}

func NewEmptyGlobError() *GlobRet {
	return &GlobRet{
		Type:              GlobRetTypeError,
		Define:            []string{},
		NewFact:           []string{},
		VerifyProcess:     []string{},
		Infer:             []string{},
		Stmt:              []string{},
		InnerGlobRetSlice: []*GlobRet{},
		Unknown:           []string{},
		Error:             []string{},
		Warnings:          []string{},
		Line:              0,
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

func NewGlobTrueWithStmt(s string) *GlobRet {
	ret := NewEmptyGlobTrue()
	ret.AddStmt(s)
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

func ErrRet(s string) *GlobRet {
	ret := NewEmptyGlobError()
	ret.AddError(s)
	return ret
}

func ErrRetWithErr(err error) *GlobRet {
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

func (m *GlobRet) Inherit(other *GlobRet) *GlobRet {
	m.Define = append(m.Define, other.Define...)
	m.NewFact = append(m.NewFact, other.NewFact...)
	m.VerifyProcess = append(m.VerifyProcess, other.VerifyProcess...)
	m.Infer = append(m.Infer, other.Infer...)
	m.Stmt = append(m.Stmt, other.Stmt...)
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

func NewGlobTrueWithStmts(stmts []string) *GlobRet {
	ret := NewEmptyGlobTrue()
	ret.Stmt = stmts
	return ret
}

func NewGlobWithInnerGlobRets(innerGlobRets []*GlobRet, msgType GlobRetType) *GlobRet {
	ret := NewEmptyGlobTrue()
	ret.InnerGlobRetSlice = innerGlobRets
	ret.Type = msgType
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

func (m *GlobRet) AddDefines(defines []string) *GlobRet {
	for _, define := range defines {
		m.AddDefine(define)
	}
	return m
}

func (m *GlobRet) AddNewFacts(newFacts []string) *GlobRet {
	for _, newFact := range newFacts {
		m.AddNewFact(newFact)
	}
	return m
}

func (m *GlobRet) AddVerifyProcesses(verifyProcesses []string) *GlobRet {
	for _, verifyProcess := range verifyProcesses {
		m.AddVerifyProcess(verifyProcess)
	}
	return m
}

func (m *GlobRet) AddInfers(infers []string) *GlobRet {
	for _, infer := range infers {
		m.AddInfer(infer)
	}
	return m
}

func (m *GlobRet) AddStmts(stmts []string) *GlobRet {
	for _, stmts := range stmts {
		m.AddStmt(stmts)
	}
	return m
}

func (m *GlobRet) AddUnknowns(unknowns []string) *GlobRet {
	for _, unknown := range unknowns {
		m.AddUnknown(unknown)
	}
	return m
}

func (m *GlobRet) AddErrors(errors []string) *GlobRet {
	for _, error := range errors {
		m.AddError(error)
	}
	return m
}

func (m *GlobRet) AddInnerGlobRets(innerGlobRets []*GlobRet) *GlobRet {
	for _, innerGlobRet := range innerGlobRets {
		m.AddInnerGlobRet(innerGlobRet)
	}
	return m
}

func (m *GlobRet) SetLine(line uint) *GlobRet {
	m.Line = line
	return m
}

func (m *GlobRet) AddWarnings(warnings []string) *GlobRet {
	for _, warning := range warnings {
		m.AddWarning(warning)
	}
	return m
}

func (m *GlobRet) AddWarning(warning string) *GlobRet {
	if warning == "" {
		return m
	}
	m.Warnings = append(m.Warnings, warning)
	return m
}
