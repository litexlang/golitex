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

package litex_verifier

// verState的工作原理类似Unix file permission
// 每个verifier方法都需要传入state，一方面是注入specMode，一方面是判断是否要打印
type VerState uint8

const (
	FinalRoundMsg VerState = iota
	FinalRoundNoMsg
	Round0Msg
	Round0NoMsg
	Round1Msg
	Round1NoMsg
)

func (e VerState) requireMsg() bool {
	if e == FinalRoundMsg || e == Round0Msg || e == Round1Msg {
		return true
	} else {
		return false
	}
}

func (e VerState) isFinalRound() bool {
	if e == FinalRoundMsg || e == FinalRoundNoMsg {
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
		return FinalRoundMsg
	case Round1NoMsg:
		return FinalRoundNoMsg
	default:
		return e
	}
}

func (e VerState) toNoMsg() VerState {
	switch e {
	case Round0Msg:
		return Round0NoMsg
	case Round1Msg:
		return Round1NoMsg
	case FinalRoundMsg:
		return FinalRoundNoMsg
	default:
		return e
	}
}

func (e VerState) toFinalRound() VerState {
	if e.requireMsg() {
		return FinalRoundMsg
	} else {
		return FinalRoundNoMsg
	}
}

// func (e VerState) isRound1() bool {
// 	if e == Round1Msg || e == Round1NoMsg {
// 		return true
// 	} else {
// 		return false
// 	}
// }
