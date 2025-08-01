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
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

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
	FinalRoundMsg_ReqOk // ReqOk 了就说明是req已经检查好了，不需要检查了
	FinalRoundNoMsg_ReqOk
	Round0Msg_ReqOk
	Round0NoMsg_ReqOk
	Round1Msg_ReqOk
	Round1NoMsg_ReqOk
)

func (e VerState) requireMsg() bool {
	if e == FinalRoundMsg || e == Round0Msg || e == Round1Msg || e == FinalRoundMsg_ReqOk || e == Round0Msg_ReqOk || e == Round1Msg_ReqOk {
		return true
	} else {
		return false
	}
}

func (e VerState) isFinalRound() bool {
	if e == FinalRoundMsg || e == FinalRoundNoMsg || e == FinalRoundMsg_ReqOk || e == FinalRoundNoMsg_ReqOk {
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
	case Round0Msg_ReqOk:
		return Round1Msg_ReqOk
	case Round0NoMsg_ReqOk:
		return Round1NoMsg_ReqOk
	case Round1Msg_ReqOk:
		return FinalRoundMsg_ReqOk
	case Round1NoMsg_ReqOk:
		return FinalRoundNoMsg_ReqOk
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
	case Round0Msg_ReqOk:
		return Round0NoMsg_ReqOk
	case Round1Msg_ReqOk:
		return Round1NoMsg_ReqOk
	case FinalRoundMsg_ReqOk:
		return FinalRoundNoMsg_ReqOk
	default:
		return e
	}
}

func (e VerState) toReqOk() VerState {
	switch e {
	case Round0Msg:
		return Round0Msg_ReqOk
	case Round1Msg:
		return Round1Msg_ReqOk
	case FinalRoundMsg:
		return FinalRoundMsg_ReqOk
	case FinalRoundNoMsg:
		return FinalRoundNoMsg_ReqOk
	case Round0NoMsg:
		return Round0NoMsg_ReqOk
	case Round1NoMsg:
		return Round1NoMsg_ReqOk
	default:
		return e
	}
}

func (e VerState) IsReqOk() bool {
	return e == FinalRoundMsg_ReqOk || e == Round0Msg_ReqOk || e == Round1Msg_ReqOk || e == FinalRoundNoMsg_ReqOk || e == Round0NoMsg_ReqOk || e == Round1NoMsg_ReqOk
}

func (e VerState) toFinalRound() VerState {
	if e.requireMsg() {
		if e.IsReqOk() {
			return FinalRoundMsg_ReqOk
		} else {
			return FinalRoundMsg
		}
	} else {
		if e.IsReqOk() {
			return FinalRoundNoMsg_ReqOk
		} else {
			return FinalRoundNoMsg
		}
	}
}

func (e VerState) String() string {
	switch e {
	case FinalRoundMsg:
		return "FinalRoundMsg"
	case FinalRoundNoMsg:
		return "FinalRoundNoMsg"
	case Round0Msg:
		return "Round0Msg"
	case Round0NoMsg:
		return "Round0NoMsg"
	case Round1Msg:
		return "Round1Msg"
	case Round1NoMsg:
		return "Round1NoMsg"
	case FinalRoundMsg_ReqOk:
		return "FinalRoundMsg_ReqOk"
	case FinalRoundNoMsg_ReqOk:
		return "FinalRoundNoMsg_ReqOk"
	case Round0Msg_ReqOk:
		return "Round0Msg_ReqOk"
	case Round0NoMsg_ReqOk:
		return "Round0NoMsg_ReqOk"
	case Round1Msg_ReqOk:
		return "Round1Msg_ReqOk"
	case Round1NoMsg_ReqOk:
		return "Round1NoMsg_ReqOk"
	default:
		return "Unknown"
	}
}
