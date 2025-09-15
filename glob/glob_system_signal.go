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

type SysSignal uint8

const (
	SysSignalTrue SysSignal = iota
	SysSignalUnknown
	SysSignalParseError
	SysSignalRuntimeError
	SysSignalSystemError
	SysSignalFalse
)

func (s SysSignal) String() string {
	switch s {
	case SysSignalTrue:
		return REPLSuccessMessage
	case SysSignalUnknown:
		return REPLUnknownMessage
	case SysSignalParseError:
		return REPLSyntaxErrorMessage
	case SysSignalRuntimeError:
		return REPLRuntimeErrorMessage
	case SysSignalSystemError:
		return REPLSystemErrorMessage
	case SysSignalFalse:
		return REPLFalseMessage
	default:
		return REPLRuntimeErrorMessage
	}
}
