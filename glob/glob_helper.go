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

package litex_global

import (
	"strconv"
	"strings"
)

func GenerateNamesLikeExcelColumnNames(n int) []string {
	names := make([]string, n)
	for i := 1; i <= n; i++ {
		names[i-1] = strconv.Itoa(i)
	}
	return names
}

// RemoveWindowsCarriage 移除 Windows 换行符中的回车符(\r)，将 CRLF 转换为 LF
// 这样可以让 Windows 格式的代码在 Unix/Linux 系统上也能正常处理
func RemoveWindowsCarriage(code string) string {
	return strings.ReplaceAll(code, "\r", "")
}

func IsKeywordSetOrNonEmptySetOrFiniteSet(s string) bool {
	return s == KeywordSet || s == KeywordNonEmptySet || s == KeywordFiniteSet
}

func GetPkgNameAndAtomName(name string) (bool, string, string) {
	parts := strings.Split(name, PkgNameAtomSeparator)
	if len(parts) != 2 {
		return false, "", ""
	}

	return true, parts[0], parts[1]
}
