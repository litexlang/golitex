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

package litex_ast

import (
	"fmt"
	"strings"
)

func (f FcAtom) ToLatexString() string {
	return fmt.Sprintf("$%s$", strings.ReplaceAll(string(f), "_", "\\_"))
}

func (f *FcFn) ToLatexString() string {
	if ok, str := isSpecialLatexSymbol_Process(f); ok {
		return str
	}

	return fmt.Sprintf("$%s$", strings.ReplaceAll(f.String(), "_", "\\_"))
}

func isSpecialLatexSymbol_Process(f *FcFn) (bool, string) {
	fHead, ok := f.FnHead.(FcAtom)
	if !ok {
		return false, ""
	}

	if len(f.Params) == 2 {
		switch string(fHead) {
		case "union":
			return true, fmt.Sprintf("%s $\\cup$ %s", f.Params[0].ToLatexString(), f.Params[1].ToLatexString())
		case "intersection":
			return true, fmt.Sprintf("%s $\\cap$ %s", f.Params[0].ToLatexString(), f.Params[1].ToLatexString())
		}
	}

	return false, ""
}
