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

type StmtRetType int8

const (
	StmtRetTypeTrue StmtRetType = iota
	StmtRetTypeUnknown
	StmtRetTypeError
)

type StmtRet struct {
	Type              StmtRetType
	Define            []string
	NewFact           []string
	VerifyProcess     []*VerMsg
	Infer             []string
	Stmt              []string
	InnerStmtRetSlice []*StmtRet
	Unknown           []string
	Error             []string
	Warnings          []string

	Line uint
}

func (m *StmtRet) String() string {
	var builder strings.Builder

	if m.Line != 0 {
		builder.WriteString(fmt.Sprintf("*** line %d ***\n\n", m.Line))
	}

	if len(m.Stmt) > 0 {
		builder.WriteString("--- statement ---\n\n")
		builder.WriteString(strings.Join(m.Stmt, "\n"))
		builder.WriteString("\n\n")
	}

	if len(m.Define) > 0 {
		builder.WriteString("--- definition ---\n\n")
		builder.WriteString(strings.Join(m.Define, "\n"))
		builder.WriteString("\n\n")
	}

	if len(m.NewFact) > 0 {
		builder.WriteString("--- new fact ---\n\n")
		builder.WriteString(strings.Join(m.NewFact, "\n"))
		builder.WriteString("\n\n")
	}

	if len(m.VerifyProcess) > 0 {
		builder.WriteString("--- verification process ---\n\n")
		for _, verifyProcess := range m.VerifyProcess {
			builder.WriteString(verifyProcess.String())
			builder.WriteString("\n\n")
		}
	}

	if len(m.Infer) > 0 {
		builder.WriteString("--- infer ---\n\n")
		builder.WriteString(strings.Join(m.Infer, "\n"))
		builder.WriteString("\n\n")
	}

	if len(m.InnerStmtRetSlice) > 0 {
		builder.WriteString("--- details ---\n\n")
		for _, innerStmtRet := range m.InnerStmtRetSlice {
			builder.WriteString(innerStmtRet.String())
			builder.WriteString("\n\n")
		}
		builder.WriteString("\n\n")
	}

	if len(m.Warnings) > 0 {
		builder.WriteString("--- warning ---\n\n")
		builder.WriteString(strings.Join(m.Warnings, "\n"))
		builder.WriteString("\n\n")
	}

	if len(m.Error) > 0 {
		if m.Line != 0 {
			builder.WriteString(fmt.Sprintf("*** line %d: error ***\n\n", m.Line))
		} else {
			builder.WriteString("*** error ***\n\n")
		}
		builder.WriteString(strings.Join(m.Error, "\n"))
		builder.WriteString("\n\n")
	} else if len(m.Unknown) > 0 {
		if m.Line != 0 {
			builder.WriteString(fmt.Sprintf("*** line %d: unknown ***\n\n", m.Line))
		} else {
			builder.WriteString("*** unable to verify ***\n\n")
		}
		builder.WriteString(strings.Join(m.Unknown, "\n"))
		builder.WriteString("\n\n")
	} else {
		if m.Line != 0 {
			builder.WriteString(fmt.Sprintf("*** line %d: success! ***\n\n", m.Line))
		} else {
			builder.WriteString("*** success! ***\n\n")
		}
	}

	return builder.String()
}

func (m *StmtRet) AddDefine(define string) *StmtRet {
	if define == "" {
		return m
	}
	m.Define = append(m.Define, define)
	return m
}

func (m *StmtRet) AddNewFact(newFact string) *StmtRet {
	if newFact == "" {
		return m
	}
	m.NewFact = append(m.NewFact, newFact)
	return m
}

func (m *StmtRet) AddVerifyProcess(verMsg *VerMsg) *StmtRet {
	m.VerifyProcess = append(m.VerifyProcess, verMsg)
	return m
}

func (m *StmtRet) AddInfer(infer string) *StmtRet {
	if infer == "" {
		return m
	}
	m.Infer = append(m.Infer, infer)
	return m
}

func (m *StmtRet) AddStmt(s string) *StmtRet {
	if s == "" {
		return m
	}
	m.Stmt = append(m.Stmt, s)
	return m
}

func (m *StmtRet) AddUnknown(unknown string) *StmtRet {
	if unknown == "" {
		return m
	}
	m.Unknown = append(m.Unknown, unknown)
	return m
}

func (m *StmtRet) AddError(error string) *StmtRet {
	if error == "" {
		return m
	}
	m.Error = append(m.Error, error)
	return m
}

func (m *StmtRet) AddInnerStmtRet(innerStmtRet *StmtRet) *StmtRet {
	if innerStmtRet == nil {
		return m
	}
	m.InnerStmtRetSlice = append(m.InnerStmtRetSlice, innerStmtRet)
	return m
}

func NewEmptyStmtTrue() *StmtRet {
	return &StmtRet{
		Type:              StmtRetTypeTrue,
		Define:            []string{},
		NewFact:           []string{},
		VerifyProcess:     []*VerMsg{},
		Infer:             []string{},
		Stmt:              []string{},
		Unknown:           []string{},
		Error:             []string{},
		InnerStmtRetSlice: []*StmtRet{},
		Warnings:          []string{},
		Line:              0,
	}
}

func NewEmptyStmtUnknown() *StmtRet {
	return &StmtRet{
		Type:              StmtRetTypeUnknown,
		Define:            []string{},
		NewFact:           []string{},
		VerifyProcess:     []*VerMsg{},
		Infer:             []string{},
		Stmt:              []string{},
		Unknown:           []string{},
		Error:             []string{},
		InnerStmtRetSlice: []*StmtRet{},
		Warnings:          []string{},
		Line:              0,
	}
}

func NewEmptyStmtError() *StmtRet {
	return &StmtRet{
		Type:              StmtRetTypeError,
		Define:            []string{},
		NewFact:           []string{},
		VerifyProcess:     []*VerMsg{},
		Infer:             []string{},
		Stmt:              []string{},
		InnerStmtRetSlice: []*StmtRet{},
		Unknown:           []string{},
		Error:             []string{},
		Warnings:          []string{},
		Line:              0,
	}
}

func NewStmtTrueWithDefine(define string) *StmtRet {
	ret := NewEmptyStmtTrue()
	ret.AddDefine(define)
	return ret
}

func NewStmtTrueWithNewFact(newFact string) *StmtRet {
	ret := NewEmptyStmtTrue()
	ret.AddNewFact(newFact)
	return ret
}

func NewStmtTrueWithVerifyProcess(verMsg *VerMsg) *StmtRet {
	ret := NewEmptyStmtTrue()
	ret.AddVerifyProcess(verMsg)
	return ret
}

func NewStmtTrueWithInfer(infer string) *StmtRet {
	ret := NewEmptyStmtTrue()
	ret.AddInfer(infer)
	return ret
}

func NewStmtTrueWithStmt(s string) *StmtRet {
	ret := NewEmptyStmtTrue()
	ret.AddStmt(s)
	return ret
}

func UnknownRet(unknown string) *StmtRet {
	ret := NewEmptyStmtUnknown()
	ret.AddUnknown(unknown)
	return ret
}

func ErrRet(s string) *StmtRet {
	ret := NewEmptyStmtError()
	ret.AddError(s)
	return ret
}

func ErrRetWithErr(err error) *StmtRet {
	ret := NewEmptyStmtError()
	ret.AddError(err.Error())
	return ret
}

func (m *StmtRet) SetType(msgType StmtRetType) *StmtRet {
	m.Type = msgType
	return m
}

func (m *StmtRet) IsTrue() bool {
	return m.Type == StmtRetTypeTrue
}

func (m *StmtRet) IsUnknown() bool {
	return m.Type == StmtRetTypeUnknown
}

func (m *StmtRet) IsErr() bool {
	return m.Type == StmtRetTypeError
}

func (m *StmtRet) IsNotTrue() bool {
	return m.Type != StmtRetTypeTrue
}

func (m *StmtRet) IsNotUnknown() bool {
	return m.Type != StmtRetTypeUnknown
}

func (m *StmtRet) IsNotError() bool {
	return m.Type != StmtRetTypeError
}

func (m *StmtRet) Inherit(other *StmtRet) *StmtRet {
	m.Define = append(m.Define, other.Define...)
	m.NewFact = append(m.NewFact, other.NewFact...)
	m.VerifyProcess = append(m.VerifyProcess, other.VerifyProcess...)
	m.Infer = append(m.Infer, other.Infer...)
	m.Stmt = append(m.Stmt, other.Stmt...)
	m.Unknown = append(m.Unknown, other.Unknown...)
	m.Error = append(m.Error, other.Error...)
	m.InnerStmtRetSlice = append(m.InnerStmtRetSlice, other.InnerStmtRetSlice...)
	return m
}

func NewStmtTrueRetWithDefines(defines []string) *StmtRet {
	ret := NewEmptyStmtTrue()
	ret.Define = defines
	return ret
}

func NewStmtTrueWithInfers(infers []string) *StmtRet {
	ret := NewEmptyStmtTrue()
	ret.Infer = infers
	return ret
}

func NewStmtTrueWithStmts(stmts []string) *StmtRet {
	ret := NewEmptyStmtTrue()
	ret.Stmt = stmts
	return ret
}

func NewStmtWithInnerStmtsRet(innerStmtsRet []*StmtRet, msgType StmtRetType) *StmtRet {
	ret := NewEmptyStmtTrue()
	ret.InnerStmtRetSlice = innerStmtsRet
	ret.Type = msgType
	return ret
}

func (m *StmtRet) AddDefineMsgs(defines []string) *StmtRet {
	for _, define := range defines {
		m.AddDefine(define)
	}
	return m
}

func (m *StmtRet) AddNewFacts(newFacts []string) *StmtRet {
	for _, newFact := range newFacts {
		m.AddNewFact(newFact)
	}
	return m
}

func (m *StmtRet) AddVerifyProcesses(verifyProcesses []*VerMsg) *StmtRet {
	for _, verifyProcess := range verifyProcesses {
		m.AddVerifyProcess(verifyProcess)
	}
	return m
}

func (m *StmtRet) AddInfers(infers []string) *StmtRet {
	for _, infer := range infers {
		m.AddInfer(infer)
	}
	return m
}

func (m *StmtRet) AddStmts(stmts []string) *StmtRet {
	for _, stmts := range stmts {
		m.AddStmt(stmts)
	}
	return m
}

func (m *StmtRet) AddUnknowns(unknowns []string) *StmtRet {
	for _, unknown := range unknowns {
		m.AddUnknown(unknown)
	}
	return m
}

func (m *StmtRet) AddErrors(errors []string) *StmtRet {
	for _, error := range errors {
		m.AddError(error)
	}
	return m
}

func (m *StmtRet) SetLine(line uint) *StmtRet {
	m.Line = line
	return m
}

func (m *StmtRet) AddWarnings(warnings []string) *StmtRet {
	for _, warning := range warnings {
		m.AddWarning(warning)
	}
	return m
}

func (m *StmtRet) AddWarning(warning string) *StmtRet {
	if warning == "" {
		return m
	}
	m.Warnings = append(m.Warnings, warning)
	return m
}

func (m *StmtRet) AddInnerStmtRets(innerStmtRetSlice []*StmtRet) *StmtRet {
	m.InnerStmtRetSlice = innerStmtRetSlice
	return m
}
