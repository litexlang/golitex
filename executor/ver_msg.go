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

func (ver *Verifier) successWithMsg(stmtStr, stmtVerifiedBy string, execRet ExecRet) ExecRet {
	execRet.AddMsg(successVerString(stmtStr, stmtVerifiedBy))
	return execRet
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

func parametersDoNotSatisfyFnReq(param ast.Obj, fnName ast.Obj) error {
	return fmt.Errorf("the arguments passed to the %s do not satisfy the domain of %s", param, fnName)
}
