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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strings"
)

func (ver *Verifier) specFactSpecMemTrueMsg(stmt *ast.SpecFactStmt, knownFact ast.SpecFactStmt) {
	var verifiedBy strings.Builder

	verifiedBy.WriteString(knownFact.StringWithLine())
	verifiedBy.WriteString("\n")
	ver.successWithMsg(stmt.String(), verifiedBy.String())
}

func (ver *Verifier) successWithMsg(stmtStr, stmtVerifiedBy string) {
	ver.env.Msgs = append(ver.env.Msgs, successVerString(stmtStr, stmtVerifiedBy))
}

func successVerString(stmtStr, stmtVerifiedBy string) string {
	var successVerString strings.Builder
	if stmtStr != "" {
		successVerString.WriteString(stmtStr)
	}
	if stmtVerifiedBy != "" {
		successVerString.WriteString(fmt.Sprintf("\nis true. proved by\n%s", stmtVerifiedBy))
	} else {
		successVerString.WriteString("\nis true.")
	}
	return successVerString.String()
}

func (ver *Verifier) newMsgAtParent(s string) error {
	if ver.env.Parent == nil {
		return fmt.Errorf("no parent env")
	} else {
		if glob.RequireMsg() {
			ver.env.Parent.Msgs = append(ver.env.Parent.Msgs, s)
		}
		return nil
	}
}

func parametersDoNotSatisfyFnReq(param ast.Fc, fnName ast.Fc) error {
	return fmt.Errorf("the arguments passed to the %s do not satisfy the domain of %s", param, fnName)
}
