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

type SysSignal uint8

const (
	SysSignalParseError SysSignal = iota
	SysSignalRuntimeError
	SysSignalTrue
	SysSignalFalse
	SysSignalUnknown
)

func (s SysSignal) String() string {
	return []string{"Finished: Syntax Error", "Finished: Runtime Error", "Finished: True", "Finished: False", "Finished: Unknown"}[s]
}
