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

import (
	"fmt"
	glob "golitex/glob"
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
		return "", fmt.Errorf("unexpected end of slice %v", strings.Join(cursor.slice, " "))
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

func (cursor *strSliceCursor) skipKwAndColon_ExceedEnd(kw string) error {
	err := cursor.skip(kw)
	if err != nil {
		return err
	}
	err = cursor.skip(glob.KeySymbolColon)
	if err != nil {
		return err
	}

	if cursor.ExceedEnd() {
		return nil
	}

	return fmt.Errorf("expected end of slice, but got '%s'", cursor.slice[cursor.index])
}

func (cursor *strSliceCursor) skipAndSkipColonAndAchieveEnd() (string, error) {
	curToken, err := cursor.currentToken()
	if err != nil {
		return "", err
	}
	err = cursor.skip()
	if err != nil {
		return "", err
	}
	err = cursor.skip(glob.KeySymbolColon)
	if err != nil {
		return "", err
	}
	if cursor.index < len(cursor.slice) {
		return "", fmt.Errorf("expected end of slice, but got '%s'", cursor.slice[cursor.index])
	}
	return curToken, nil
}
