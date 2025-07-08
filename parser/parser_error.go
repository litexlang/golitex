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

package litex_parser

import (
	"fmt"
)

func tbErr(previousErr error, stmt *tokenBlock) error {
	if curTok, err := stmt.header.currentToken(); err == nil {
		return fmt.Errorf("parse error:\nline \"%s\", error at \"%s\"\nerror block:\n%s\n%w", &stmt.header, curTok, stmt, previousErr)
	} else {
		return fmt.Errorf("parse error:\nline \"%s\", error at end of statement\nerror block:\n%s\n%w", &stmt.header, stmt, previousErr)
	}
}
