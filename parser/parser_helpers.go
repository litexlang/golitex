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

package litex_parser

import (
	"fmt"
	glob "golitex/glob"
)

// expectAndSkipCommaOr checks the next token after an item:
// - if it's a comma, it skips it and returns (done=false, nil)
// - if it's the expected end token, it returns (done=true, nil)
// - otherwise, returns an error
func (tb *tokenBlock) expectAndSkipCommaOr(endToken string) (bool, error) {
	if tb.header.is(glob.KeySymbolComma) {
		tb.header.skip(glob.KeySymbolComma)
		return false, nil
	}
	if !tb.header.is(endToken) {
		return false, tbErr(fmt.Errorf("expected '%s' but got '%s'", endToken, tb.header.strAtCurIndexPlus(0)), tb)
	}
	return true, nil
}
