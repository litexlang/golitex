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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
	"strings"
)

func (ver *Verifier) successMsgEnd(stmtStr, stmtVerifiedBy string) {
	if stmtStr != "" {
		ver.env.Msgs = append(ver.env.Msgs, stmtStr)
	}
	if stmtVerifiedBy != "" {
		message := fmt.Sprintf("is true. proved by\n%v", stmtVerifiedBy)
		ver.env.Msgs = append(ver.env.Msgs, message)
	} else {
		message := "is true."
		ver.env.Msgs = append(ver.env.Msgs, message)
	}
}

func (ver *Verifier) newMsgEnd(format string, args ...any) {
	message := fmt.Sprintf(format, args...)
	ver.env.Msgs = append(ver.env.Msgs, message)
}

func (ver *Verifier) specFactSpecMemTrueMsg(stmt *ast.SpecFactStmt, knownFact env.KnownSpecFact) {
	var verifiedBy strings.Builder

	verifiedBy.WriteString(knownFact.String())
	verifiedBy.WriteString("\n")
	for i, knownParam := range knownFact.Fact.Params {
		verifiedBy.WriteString(fmt.Sprintf("%s matches %s\n", knownParam, stmt.Params[i]))
	}
	ver.successWithMsg(stmt.String(), verifiedBy.String())
}

func (ver *Verifier) newMsgEndWithCurMatchProp(stmt *ast.SpecFactStmt, knownFact env.KnownSpecFact, knownPreviousSuppose *ast.SpecFactStmt) {
	var verifiedBy strings.Builder

	if knownPreviousSuppose != nil {
		verifiedBy.WriteString(fmt.Sprintf("known %s/%s %s:\n", glob.KeywordWith, glob.KeywordSuppose, knownPreviousSuppose.String()))
		verifiedBy.WriteString(glob.SplitLinesAndAdd4NIndents(knownFact.String(), 1))
		verifiedBy.WriteString("\n")
	}

	for i, knownParam := range knownFact.Fact.Params {
		// Have to write matches, because in with-suppose situation, the param is not literally equal to the stmt param
		verifiedBy.WriteString(fmt.Sprintf("%s matches %s\n", knownParam, stmt.Params[i]))
	}
	ver.successWithMsg(stmt.String(), verifiedBy.String())
}
