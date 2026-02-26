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

import (
	"fmt"
	"strings"
)

type VerRet interface {
	verRet()
	IsTrue() bool
	IsUnknown() bool
	IsErr() bool
	IsNotTrue() bool
	ToStmtRet() StmtRet
	AddExtraInfo(extraInfo string) VerRet
	AddExtraInfos(extraInfos []string) VerRet
	GetExtraInfos() []string
	GetToCheck() FactStmt
	String() string
}

type TrueVerRet struct {
	ToCheck                FactStmt
	VerifiedByKnownFact    FactStmt
	VerifiedByBuiltinRules string
	ExtraInfo              []string
}

func (r *TrueVerRet) verRet()         {}
func (r *TrueVerRet) IsTrue() bool    { return true }
func (r *TrueVerRet) IsUnknown() bool { return false }
func (r *TrueVerRet) IsErr() bool     { return false }
func (r *TrueVerRet) IsNotTrue() bool { return false }

type UnknownVerRet struct {
	ToCheck   FactStmt
	ExtraInfo []string
}

func (r *UnknownVerRet) verRet()         {}
func (r *UnknownVerRet) IsTrue() bool    { return false }
func (r *UnknownVerRet) IsUnknown() bool { return true }
func (r *UnknownVerRet) IsErr() bool     { return false }
func (r *UnknownVerRet) IsNotTrue() bool { return true }

type ErrVerRet struct {
	ToCheck   FactStmt
	ExtraInfo []string
}

func (r *ErrVerRet) verRet()         {}
func (r *ErrVerRet) IsTrue() bool    { return false }
func (r *ErrVerRet) IsUnknown() bool { return false }
func (r *ErrVerRet) IsErr() bool     { return true }
func (r *ErrVerRet) IsNotTrue() bool { return true }

func NewTrueVerRet(ToCheck FactStmt, VerifiedByKnownFact FactStmt, VerifiedByBuiltinRules string) *TrueVerRet {
	return &TrueVerRet{ToCheck: ToCheck, VerifiedByKnownFact: VerifiedByKnownFact, VerifiedByBuiltinRules: VerifiedByBuiltinRules}
}

func NewUnknownVerRet(ToCheck FactStmt) *UnknownVerRet {
	return &UnknownVerRet{ToCheck: ToCheck}
}

func NewErrVerRet(ToCheck FactStmt) *ErrVerRet {
	return &ErrVerRet{ToCheck: ToCheck}
}

func NewEmptyVerRetErr() *ErrVerRet {
	return &ErrVerRet{ToCheck: nil}
}

// func NewEmptyUnknownVerRet() *UnknownVerRet {
// 	return &UnknownVerRet{ToCheck: nil}
// }

func (r *TrueVerRet) ToStmtRet() StmtRet {
	return NewTrueStmtEmptyRet(r.ToCheck).AddVerifyProcess(r)
}
func (r *UnknownVerRet) ToStmtRet() StmtRet {
	return NewUnknownStmtEmptyRet(r.ToCheck)
}
func (r *ErrVerRet) ToStmtRet() StmtRet {
	return NewErrStmtEmptyRet(r.ToCheck)
}

func (r *UnknownVerRet) AddExtraInfo(extraInfo string) VerRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfo)
	return r
}
func (r *ErrVerRet) AddExtraInfo(extraInfo string) VerRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfo)
	return r
}
func (r *ErrVerRet) AddErr(err error) *ErrVerRet {
	r.ExtraInfo = append(r.ExtraInfo, err.Error())
	return r
}

func (r *TrueVerRet) AddExtraInfos(extraInfos []string) VerRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfos...)
	return r
}

func (r *TrueVerRet) GetExtraInfos() []string {
	return r.ExtraInfo
}

func (r *UnknownVerRet) AddExtraInfos(extraInfos []string) VerRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfos...)
	return r
}
func (r *UnknownVerRet) GetExtraInfos() []string {
	return r.ExtraInfo
}
func (r *ErrVerRet) AddExtraInfos(extraInfos []string) VerRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfos...)
	return r
}
func (r *ErrVerRet) GetExtraInfos() []string {
	return r.ExtraInfo
}

func (r *TrueVerRet) AddExtraInfo(extraInfo string) VerRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfo)
	return r
}

func (r *TrueVerRet) GetToCheck() FactStmt {
	return r.ToCheck
}
func (r *UnknownVerRet) GetToCheck() FactStmt {
	return r.ToCheck
}
func (r *ErrVerRet) GetToCheck() FactStmt {
	return r.ToCheck
}

func (r *TrueVerRet) String() string {
	var builder strings.Builder
	if r.ToCheck == nil {
		builder.WriteString("some fact is true")
	} else {
		builder.WriteString(fmt.Sprintf("true:\n%s\n", r.ToCheck.String()))
	}

	if r.VerifiedByKnownFact != nil {
		builder.WriteString(fmt.Sprintf("verified by known fact on line %d:\n%s\n", r.VerifiedByKnownFact.GetLine(), r.VerifiedByKnownFact.String()))
	} else if r.VerifiedByBuiltinRules != "" {
		builder.WriteString(fmt.Sprintf("verified by builtin rules:\n%s\n", r.VerifiedByBuiltinRules))
	}

	if len(r.ExtraInfo) > 0 {
		builder.WriteString("\n\nExtra Info:\n")
		for _, extraInfo := range r.ExtraInfo {
			builder.WriteString(extraInfo)
			builder.WriteString("\n")
		}
	}

	return builder.String()
}

func (r *UnknownVerRet) String() string {
	var builder strings.Builder
	if r.ToCheck == nil {
		builder.WriteString("some fact is unknown")
	} else {
		builder.WriteString(fmt.Sprintf("unknown:\n%s\n", r.ToCheck.String()))
	}

	if len(r.ExtraInfo) > 0 {
		builder.WriteString("\n\nExtra Info:\n")
		for _, extraInfo := range r.ExtraInfo {
			builder.WriteString(extraInfo)
			builder.WriteString("\n")
		}
	}

	return builder.String()
}
func (r *ErrVerRet) String() string {
	var builder strings.Builder
	if r.ToCheck == nil {
		builder.WriteString("some fact is error")
	} else {
		builder.WriteString(fmt.Sprintf("error:\n%s\n", r.ToCheck.String()))
	}

	if len(r.ExtraInfo) > 0 {
		builder.WriteString("\n\nExtra Info:\n")
		for _, extraInfo := range r.ExtraInfo {
			builder.WriteString(extraInfo)
			builder.WriteString("\n")
		}
	}

	return builder.String()
}
