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
	glob "golitex/glob"
	"strings"
)

func (f Atom) ToLatexString() string {
	switch string(f) {
	case glob.KeywordReal:
		return "$\\mathbb{R}$"
	case glob.KeywordNatural:
		return "$\\mathbb{N}$"
	case glob.KeywordInteger:
		return "$\\mathbb{Z}$"
	case glob.KeywordRational:
		return "$\\mathbb{Q}$"
	case glob.KeywordNPos:
		return "$\\mathbb{N}^{+}$"
	default:
		return fmt.Sprintf("$%s$", strings.ReplaceAll(string(f), "_", "\\_"))
	}
}

func (f *FnObj) ToLatexString() string {
	if ok, str := isSpecialLatexSymbol_Process(f); ok {
		return str
	}

	head := strings.ReplaceAll(f.FnHead.ToLatexString(), "$", "")
	paramSlice := make([]string, len(f.Params))
	for i, param := range f.Params {
		paramSlice[i] = strings.ReplaceAll(param.ToLatexString(), "$", "")
	}
	return fmt.Sprintf("$%s(%s)$", head, strings.Join(paramSlice, ", "))
}

func isSpecialLatexSymbol_Process(f *FnObj) (bool, string) {
	fHead, ok := f.FnHead.(Atom)
	if !ok {
		return false, ""
	}

	if len(f.Params) == 2 {
		switch string(fHead) {
		case "union":
			return true, fmt.Sprintf("%s $\\cup$ %s", f.Params[0].ToLatexString(), f.Params[1].ToLatexString())
		case "intersection":
			return true, fmt.Sprintf("%s $\\cap$ %s", f.Params[0].ToLatexString(), f.Params[1].ToLatexString())
		case "^":
			left := strings.ReplaceAll(f.Params[0].ToLatexString(), "$", "")
			right := strings.ReplaceAll(f.Params[1].ToLatexString(), "$", "")
			return true, fmt.Sprintf("$%s^{%s}$", left, right)
		case "+":
			return true, fmt.Sprintf("%s $+$ %s", f.Params[0].ToLatexString(), f.Params[1].ToLatexString())
		case "*":
			return true, fmt.Sprintf("%s $*$ %s", f.Params[0].ToLatexString(), f.Params[1].ToLatexString())
		case "-":
			return true, fmt.Sprintf("%s $-$ %s", f.Params[0].ToLatexString(), f.Params[1].ToLatexString())
		case "/":
			return true, fmt.Sprintf("%s $\\div$ %s", f.Params[0].ToLatexString(), f.Params[1].ToLatexString())
		case "%":
			return true, fmt.Sprintf("%s $\\%%$ %s", f.Params[0].ToLatexString(), f.Params[1].ToLatexString())
		}
	}

	return false, ""
}
