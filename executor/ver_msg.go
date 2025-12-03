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
	"strings"
)

func successVerString(stmt, stmtVerifiedBy ast.Stmt) string {
	var builder strings.Builder
	if stmt != nil {
		builder.WriteString(stmt.String())
	}
	if stmtVerifiedBy != nil {
		builder.WriteString(fmt.Sprintf("\nis true. proved by fact on line %d:\n%s", stmtVerifiedBy.GetLine(), stmtVerifiedBy.String()))
	} else {
		builder.WriteString("\nis true.")
	}
	return builder.String()
}

// successVerStringString is a helper function for backward compatibility with string-based calls
func successVerStringString(stmtStr, stmtVerifiedByStr string) string {
	var builder strings.Builder
	if stmtStr != "" {
		builder.WriteString(stmtStr)
	}
	if stmtVerifiedByStr != "" {
		builder.WriteString(fmt.Sprintf("\nis true. proved by\n%s", stmtVerifiedByStr))
	} else {
		builder.WriteString("\nis true.")
	}
	return builder.String()
}
