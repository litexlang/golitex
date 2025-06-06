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

package litex_parser

type uniFactEnum uint8

const (
	UniFactDepth0 uniFactEnum = iota
	UniFactDepth1
	UniFactDepth2
)

func (enum uniFactEnum) allowMoreDepth() bool {
	return enum == UniFactDepth0 || enum == UniFactDepth1
}

func (enum uniFactEnum) addDepth() uniFactEnum {
	switch enum {
	case UniFactDepth0:
		return UniFactDepth1
	case UniFactDepth1:
		return UniFactDepth2
	}
	return enum
}
