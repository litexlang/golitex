// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_verifier

import (
	"fmt"
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
