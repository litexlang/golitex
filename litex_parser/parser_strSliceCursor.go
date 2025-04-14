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

package litex_parser

import (
	"fmt"
	"strings"
)

// strSliceCursor 表示字符串切片的游标
type strSliceCursor struct {
	index int
	slice []string
}

func (cursor *strSliceCursor) String() string {
	return strings.Join(cursor.slice, " ")
}

func (cursor *strSliceCursor) ExceedEnd() bool {
	return cursor.index >= len(cursor.slice)
}

func (cursor *strSliceCursor) strAtIndex(index uint32) string {
	return cursor.slice[index]
}

func (cursor *strSliceCursor) strAtCurIndexPlus(plusIndex int) string {
	i := cursor.index + plusIndex

	if i < 0 || i >= len(cursor.slice) {
		return ""
	} else {
		return cursor.slice[i]
	}
}

func (cursor *strSliceCursor) getIndex() int {
	return cursor.index
}

func (cursor *strSliceCursor) getSlice() []string {
	return cursor.slice
}

func (cursor *strSliceCursor) currentToken() (string, error) {
	if cursor.index >= len(cursor.slice) {
		return "", fmt.Errorf("unexpected end of slice %v", cursor.slice)
	}
	return cursor.slice[cursor.index], nil
}

func (cursor *strSliceCursor) testAndSkip(s string) error {
	if cursor.index >= len(cursor.slice) {
		return fmt.Errorf("unexpected end of slice %v", cursor.slice)
	}
	if cursor.slice[cursor.index] == s {
		cursor.index++
		return nil
	}
	return fmt.Errorf("expected '%s', but got '%s'", s, cursor.slice[cursor.index])
}

func (cursor *strSliceCursor) next() (string, error) {
	if cursor.index >= len(cursor.slice) {
		return "", fmt.Errorf("unexpected end of slice %v", cursor.slice)
	}
	cursor.index++
	return cursor.slice[cursor.index-1], nil
}

func (cursor *strSliceCursor) is(s string) bool {
	return cursor.index < len(cursor.slice) && cursor.slice[cursor.index] == s
}

func (cursor *strSliceCursor) isAndSkip(expected string) bool {
	if cursor.index < len(cursor.slice) && cursor.slice[cursor.index] == expected {
		cursor.index++
		return true
	} else {
		return false
	}
}

func (cursor *strSliceCursor) skipIfIs(s string) {
	if cursor.index < len(cursor.slice) && cursor.slice[cursor.index] == s {
		cursor.index++
	}
}

func (cursor *strSliceCursor) skip(expected ...string) error {
	if cursor.index >= len(cursor.slice) {
		return fmt.Errorf("unexpected end of slice %v", cursor.slice)
	}

	if len(expected) == 0 {
		cursor.index++
		return nil
	}

	if cursor.slice[cursor.index] == expected[0] {
		cursor.index++
	} else {
		return fmt.Errorf("expected '%s', but got '%s'", expected[0], cursor.slice[cursor.index])
	}

	return nil
}

func (cursor *strSliceCursor) curTokenBeginWithNumber() bool {
	if cursor.index >= len(cursor.slice) {
		return false
	}

	if cursor.slice[cursor.index][0] >= '0' && cursor.slice[cursor.index][0] <= '9' {
		return true
	} else {
		return false
	}
}
