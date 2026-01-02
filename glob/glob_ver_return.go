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

type VerRet struct {
	RetType            StmtRetType
	StmtStr            string
	ProvedByFactOnLine uint
	VerifyMsgs         []string
}

func NewVerMsg(retType StmtRetType, stmtStr string, provedByFactOnLine uint, verifyMsgs []string) *VerRet {
	return &VerRet{
		RetType:            retType,
		StmtStr:            stmtStr,
		ProvedByFactOnLine: provedByFactOnLine,
		VerifyMsgs:         verifyMsgs,
	}
}

func NewEmptyVerRetUnknown() *VerRet {
	return &VerRet{
		RetType:            StmtRetTypeUnknown,
		StmtStr:            "",
		ProvedByFactOnLine: 0,
		VerifyMsgs:         []string{},
	}
}

func NewEmptyVerRetTrue() *VerRet {
	return &VerRet{
		RetType:            StmtRetTypeTrue,
		StmtStr:            "",
		ProvedByFactOnLine: 0,
		VerifyMsgs:         []string{},
	}
}

func NewEmptyVerRetErr() *VerRet {
	return &VerRet{
		RetType:            StmtRetTypeError,
		StmtStr:            "",
		ProvedByFactOnLine: 0,
		VerifyMsgs:         []string{},
	}
}

func (m *VerRet) String() string {
	if m.IsTrue() {
		if m.ProvedByFactOnLine == 0 {
			if m.StmtStr == "" {
				return fmt.Sprintf("proved by builtin rules:\n%s", strings.Join(m.VerifyMsgs, "\n"))
			}
			return fmt.Sprintf("%s\nproved by builtin rules:\n%s", m.StmtStr, strings.Join(m.VerifyMsgs, "\n"))
		}

		if m.StmtStr == "" {
			return fmt.Sprintf("proved by fact stored on line %d:\n%s", m.ProvedByFactOnLine, strings.Join(m.VerifyMsgs, "\n"))
		}
		return fmt.Sprintf("%s\nproved by fact stored on line %d:\n%s", m.StmtStr, m.ProvedByFactOnLine, strings.Join(m.VerifyMsgs, "\n"))
	} else {
		if m.StmtStr == "" {
			return fmt.Sprintf("failed to verify:\n%s", strings.Join(m.VerifyMsgs, "\n"))
		}
		return fmt.Sprintf("%s\nfailed to verify:\n%s", m.StmtStr, strings.Join(m.VerifyMsgs, "\n"))
	}
}

func (m *VerRet) IsUnknown() bool {
	return m.RetType == StmtRetTypeUnknown
}

func (m *VerRet) IsTrue() bool {
	return m.RetType == StmtRetTypeTrue
}

func (m *VerRet) IsErr() bool {
	return m.RetType == StmtRetTypeError
}

func (m *VerRet) IsNotTrue() bool {
	return m.RetType != StmtRetTypeTrue
}

func (m *VerRet) IsNotUnknown() bool {
	return m.RetType != StmtRetTypeUnknown
}

func (m *VerRet) IsNotError() bool {
	return m.RetType != StmtRetTypeError
}

// ToStmtRet converts VerRet to StmtRet for compatibility
func (m *VerRet) ToStmtRet() *StmtRet {
	ret := &StmtRet{
		RetType:           m.RetType,
		Define:            []string{},
		NewFact:           []string{},
		VerifyProcess:     []*VerRet{m},
		Infer:             []string{},
		Stmt:              []string{},
		InnerStmtRetSlice: []*StmtRet{},
		Unknown:           []string{},
		Error:             []string{},
		Warnings:          []string{},
		Line:              m.ProvedByFactOnLine,
	}

	if m.RetType == StmtRetTypeUnknown {
		ret.Unknown = m.VerifyMsgs
	} else if m.RetType == StmtRetTypeError {
		ret.Error = m.VerifyMsgs
	}

	return ret
}

func (m *VerRet) AddError(s string) *VerRet {
	m.RetType = StmtRetTypeError
	m.VerifyMsgs = append(m.VerifyMsgs, s)
	return m
}

func (m *VerRet) AddUnknown(unknown string) *VerRet {
	m.RetType = StmtRetTypeUnknown
	m.VerifyMsgs = append(m.VerifyMsgs, unknown)
	return m
}

func NewErrVerRet(s string) *VerRet {
	verRet := NewEmptyVerRetErr()
	verRet.VerifyMsgs = append(verRet.VerifyMsgs, s)
	return verRet
}

func NewUnknownVerRet(s string) *VerRet {
	verRet := NewEmptyVerRetUnknown()
	verRet.VerifyMsgs = append(verRet.VerifyMsgs, s)
	return verRet
}

func NewTrueVerRetWithMsg(s string) *VerRet {
	verRet := NewEmptyVerRetTrue()
	verRet.VerifyMsgs = append(verRet.VerifyMsgs, s)
	return verRet
}

func (m *VerRet) AddVerifyMsg(s string) *VerRet {
	m.VerifyMsgs = append(m.VerifyMsgs, s)
	return m
}
