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

package litex_global

import (
	"fmt"
	"strings"
)

var REPLSuccessMessage = "Success! :)\n"
var REPLErrorMessage = "Error :(\n"
var REPLUnknownMessage = "Unknown :(\n"

func SplitLinesAndAdd4NIndents(line string, n uint32) string {
	if n == 0 {
		return line
	}

	spaces := strings.Repeat(Scope4Indents, int(n))
	lines := strings.Split(line, "\n")

	var builder strings.Builder
	// 预分配空间：原长度 + 缩进空间（每行4n个空格）
	builder.Grow(len(line) + len(spaces)*len(lines))

	// 处理第一行
	if len(lines) > 0 {
		builder.WriteString(spaces)
		builder.WriteString(lines[0])
	}

	// 处理剩余行
	for _, part := range lines[1:] {
		builder.WriteByte('\n')
		builder.WriteString(spaces)
		builder.WriteString(part)
	}

	return builder.String()
}

func InternalWarningMsg(s string, args ...any) string {
	return fmt.Sprintf("Internal Warning:\n%s\n\n", fmt.Sprintf(s, args...))
}

func WarningMsg(s string, args ...any) string {
	return fmt.Sprintf("Warning:\n%s\n\n", fmt.Sprintf(s, args...))
}

func NotImplementedMsg(s string, args ...any) string {
	return fmt.Sprintf("Feature Not Implemented (Will be implemented in the future):\n%s\n\n", fmt.Sprintf(s, args...))
}

// func InferMsgs(msg []string) string {
// 	if len(msg) == 0 {
// 		return ""
// 	}
// 	return fmt.Sprintf("infer:\n%s\n", strings.Join(msg, "\n"))
// }

func InferMsg(msg string) string {
	if msg == "" {
		return ""
	}
	return fmt.Sprintf("infer:\n%s\n", msg)
}

func IsANewObjectMsg(obj string) string {
	return fmt.Sprintf("%s is a new object", obj)
}

func IsANewPropMsg(prop string) string {
	return fmt.Sprintf("%s is a new %s", prop, KeywordProp)
}

func IsANewExistPropMsg(existProp string) string {
	return fmt.Sprintf("%s is a new %s", existProp, KeywordExistProp)
}

func IsANewFnSetMsg(fnSet string) string {
	return fmt.Sprintf("%s is a new %s", fnSet, KeywordFnSet)
}

func VerifyProcessMsgs(msgs []string) string {
	if len(msgs) == 0 {
		return ""
	}
	return fmt.Sprintf("verify process:\n%s\n", strings.Join(msgs, "\n"))
}

func AddREPLSuccessMsg(ret *StmtRet) string {
	switch ret.RetType {
	case StmtRetTypeTrue:
		return REPLSuccessMessage
	case StmtRetTypeUnknown:
		return REPLUnknownMessage
	case StmtRetTypeError:
		return REPLErrorMessage
	}
	return REPLErrorMessage
}

func REPLSuccessMsgs(t StmtRetType) string {
	switch t {
	case StmtRetTypeTrue:
		return REPLSuccessMessage
	case StmtRetTypeUnknown:
		return REPLUnknownMessage
	case StmtRetTypeError:
		return REPLErrorMessage
	}
	return REPLErrorMessage
}
