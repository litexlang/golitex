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

package litex_global

type Mem[T any] map[string]map[string]T

func (m Mem[T]) Set(key1, key2 string, value T) {
	if _, ok := m[key1]; !ok {
		m[key1] = make(map[string]T)
	}
	m[key1][key2] = value
}

func (m Mem[T]) Get(key1, key2 string) (T, bool) {
	if innerMap, ok := m[key1]; ok {
		if val, ok := innerMap[key2]; ok {
			return val, true
		}
	}
	var zero T
	return zero, false
}
