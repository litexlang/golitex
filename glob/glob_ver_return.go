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

func NewVerMsg(retType StmtRetType, stmtStr string, line uint, verifyMsgs []string) *VerRet {
	return &VerRet{
		RetType:            retType,
		StmtStr:            stmtStr,
		ProvedByFactOnLine: line,
		VerifyMsgs:         verifyMsgs,
	}
}

func (m *VerRet) String() string {
	if m.RetType == StmtRetTypeTrue {
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
