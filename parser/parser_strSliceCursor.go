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
// Litex discord server: https://discord.gg/uvrHM7eS

package litex_parser

import (
	"fmt"
	glob "golitex/glob"
	"strings"
)

// strSliceCursor 表示字符串切片的游标
// 包名的map。我在parse的时候需要清楚现在的报名被import到另外一个包的时候，它的新报名叫什么。本质上应该让这一个field跟着tokenblock，甚至做成global。在项目一开始的时候，我根据项目的config文件，或者按照import的包的方式，或者其他什么方式，来初始化这个map。或许我也应该像go一样，在parse前还有一个更前面的stage，就是建立pkgMap的stage。我先读每个文件的import指令
// 之后考虑像env一样，做的更加独立一点，或构建一个数据结构，parser里面含有 parser_env,这个parser_env里有pkgMap，然后parser_env可以作为参数传入parser的各个函数中。即在tokenblock和stmt阶段之间，有个新数据结构，用来存非执行型语句的中间结果。现在先这么搞着再说，反正我暂时也没多进程。
type strSliceCursor struct {
	index     int
	slice     []string
	parserEnv *ParserEnv // 传指针的好处是，可以对里面的东西进行修改
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

func (cursor *strSliceCursor) IsTokenAtIndexGivenWord(index int, s string) bool {
	return index < len(cursor.slice) && cursor.slice[index] == s
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

func (cursor *strSliceCursor) skip(expected string) error {
	if cursor.index >= len(cursor.slice) {
		return fmt.Errorf("unexpected end of slice %v", cursor.slice)
	}

	if expected == "" {
		cursor.index++
		return nil
	}

	if cursor.slice[cursor.index] == expected {
		cursor.index++
	} else {
		return fmt.Errorf("expected '%s', but got '%s'", expected, cursor.slice[cursor.index])
	}

	return nil
}

// func (cursor *strSliceCursor) getAndSkip(expected string) (string, error) {
// 	if cursor.index >= len(cursor.slice) {
// 		return "", fmt.Errorf("unexpected end of slice %v", cursor.slice)
// 	}

// 	curToken := cursor.slice[cursor.index]

// 	if expected == "" {
// 		cursor.index++
// 		return curToken, nil
// 	}

// 	if cursor.slice[cursor.index] == expected {
// 		cursor.index++
// 		return curToken, nil
// 	} else {
// 		return "", fmt.Errorf("expected '%s', but got '%s'", expected, cursor.slice[cursor.index])
// 	}
// }

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
	err = cursor.skip("")
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
