/*
 * Copyright 2024 Jiachen Shen.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
 * Visit litexlang.org and https://github.com/litexlang/golitex for more information.
 */

package litex_verifier

// verState的工作原理类似Unix file permission
// 每个verifier方法都需要传入state，一方面是注入specMode，一方面是判断是否要打印
type VerState uint8

const (
	SpecMsg VerState = iota
	SpecNoMsg
	Round0Msg
	Round0NoMsg
	Round1Msg
	Round1NoMsg
)

func (e VerState) requireMsg() bool {
	if e == SpecMsg || e == Round0Msg || e == Round1Msg {
		return true
	} else {
		return false
	}
}

func (e VerState) isSpec() bool {
	if e == SpecMsg || e == SpecNoMsg {
		return true
	} else {
		return false
	}
}

func (e VerState) addRound() VerState {
	switch e {
	case Round0Msg:
		return Round1Msg
	case Round0NoMsg:
		return Round1NoMsg
	case Round1Msg:
		return SpecMsg
	case Round1NoMsg:
		return SpecNoMsg
	default:
		return e
	}
}
