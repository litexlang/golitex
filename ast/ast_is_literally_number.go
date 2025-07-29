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

import "unicode"

func IsFcLiterallyNPosNumber(fc Fc) bool {
	atom, ok := fc.(FcAtom)
	if !ok {
		return false
	}
	s := string(atom)
	if len(s) == 0 {
		return false
	}

	for _, c := range s {
		if !(c >= '0' && c <= '9') {
			return false
		}
	}

	return s[0] != '0'
}

func IsFcLiterallyNatNumber(fc Fc) bool {
	atom, ok := fc.(FcAtom)
	if !ok {
		return false
	}
	s := string(atom)
	if len(s) == 0 {
		return false
	}

	for _, c := range s {
		if !(c >= '0' && c <= '9') {
			return false
		}
	}

	return true
}

func IsFcLiterallyIntNumber(fc Fc) bool {
	atom, ok := fc.(FcAtom)
	if !ok {
		return false
	}

	s := string(atom)
	if len(s) == 0 {
		return false
	}

	if s[0] == '-' {
		s = s[1:]
		if len(s) == 0 {
			return false
		}
	}

	for _, c := range s {
		if !(c >= '0' && c <= '9') {
			return false
		}
	}

	return true
}

func IsFcLiterallyRationalNumber(fc Fc) bool {
	atom, ok := fc.(FcAtom)
	if !ok {
		return false
	}

	s := string(atom)
	if len(s) == 0 {
		return false
	}

	if s[0] == '-' {
		s = s[1:]
		if len(s) == 0 {
			return false
		}
	}

	dotCount := 0
	for i, c := range s {
		if c == '.' {
			dotCount++
			if dotCount > 1 {
				return false
			}
			// 小数点不能出现在开头或结尾
			if i == 0 || i == len(s)-1 {
				return false
			}
		} else if !unicode.IsDigit(c) {
			return false
		}
	}

	return true
}
