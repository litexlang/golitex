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

package litex_global

import (
	"crypto/rand"
	"math/big"
)

func RandomString(length int) string {
	const letters = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
	result := make([]byte, length)
	for i := range result {
		n, _ := rand.Int(rand.Reader, big.NewInt(int64(len(letters))))
		result[i] = letters[n.Int64()]
	}
	return string(result)
}

func GenerateUniqueRandomStrings(n int) []string {
	uniqueStrings := make([]string, 0, n) // 使用容量n的空切片
	seen := make(map[string]bool)

	for len(uniqueStrings) < n {
		s := RandomString(4)
		if !seen[s] {
			seen[s] = true
			uniqueStrings = append(uniqueStrings, s)
		}
	}

	return uniqueStrings
}

func GenerateUniqueRandomStrings_NotInGivenStrSlice(n int, notIn []string) []string {
	uniqueStrings := make([]string, 0, n) // 使用容量n的空切片
	seen := make(map[string]bool)

	for notInItem := range notIn {
		seen[notIn[notInItem]] = true
	}

	for len(uniqueStrings) < n {
		s := RandomString(4)
		if !seen[s] {
			seen[s] = true
			uniqueStrings = append(uniqueStrings, s)
		}
	}

	return uniqueStrings
}
