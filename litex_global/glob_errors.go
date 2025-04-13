// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_global

import (
	"fmt"
	"strings"
)

type ErrLink struct {
	next error // Last in First out
	msg  string
}

func (e *ErrLink) Error() string {
	var builder strings.Builder

	builder.WriteString(e.msg)
	previous := e.next

	if previous != nil {
		builder.WriteByte('\n')
		builder.WriteString(previous.Error())
	}

	return builder.String()
}

func NewErrLink(next error, msg string, a ...any) *ErrLink {
	return &ErrLink{next, fmt.Sprintf(msg, a...)}
}

func InterpreterBug(msg string, a ...any) error {
	return fmt.Errorf(msg, a...)
}

func NewErrLinkAtFunc(next error, funcName string, msg string, a ...any) *ErrLink {
	if msg == "" {
		return NewErrLink(next, "error at %s", funcName)
	}
	return NewErrLink(NewErrLink(next, msg, a...), "error at %s", funcName)
}
