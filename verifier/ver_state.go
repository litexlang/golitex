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

import "fmt"

type VerState struct {
	Round   uint8
	WithMsg bool
	ReqOk   bool
}

func (s *VerState) addRound() *VerState {
	return &VerState{
		Round:   s.Round + 1,
		WithMsg: s.WithMsg,
		ReqOk:   s.ReqOk,
	}
}

func (s *VerState) toNoMsg() *VerState {
	return &VerState{
		Round:   s.Round,
		WithMsg: false,
		ReqOk:   s.ReqOk,
	}
}

func (s *VerState) toReqOk() *VerState {
	return &VerState{
		Round:   s.Round,
		WithMsg: s.WithMsg,
		ReqOk:   true,
	}
}

func (s *VerState) isFinalRound() bool {
	return s.Round >= 2 // return s.Round == 2
}

func (s *VerState) toFinalRound() *VerState {
	return &VerState{
		Round:   2,
		WithMsg: s.WithMsg,
		ReqOk:   s.ReqOk,
	}
}

func (s *VerState) String() string {
	if s.WithMsg {
		return fmt.Sprintf("Round %d with msg", s.Round)
	} else {
		return fmt.Sprintf("Round %d without msg", s.Round)
	}
}

var (
	Round0Msg             = &VerState{Round: 0, WithMsg: true, ReqOk: false}
	Round0NoMsg           = &VerState{Round: 0, WithMsg: false, ReqOk: false}
	Round1Msg             = &VerState{Round: 1, WithMsg: true, ReqOk: false}
	Round1NoMsg           = &VerState{Round: 1, WithMsg: false, ReqOk: false}
	FinalRoundMsg         = &VerState{Round: 2, WithMsg: true, ReqOk: false}
	FinalRoundNoMsg       = &VerState{Round: 2, WithMsg: false, ReqOk: false}
	FinalRoundMsg_ReqOk   = &VerState{Round: 2, WithMsg: true, ReqOk: true}
	FinalRoundNoMsg_ReqOk = &VerState{Round: 2, WithMsg: false, ReqOk: true}
	Round0Msg_ReqOk       = &VerState{Round: 0, WithMsg: true, ReqOk: true}
	Round0NoMsg_ReqOk     = &VerState{Round: 0, WithMsg: false, ReqOk: true}
	Round1Msg_ReqOk       = &VerState{Round: 1, WithMsg: true, ReqOk: true}
	Round1NoMsg_ReqOk     = &VerState{Round: 1, WithMsg: false, ReqOk: true}
)

func (s *VerState) requireMsg() bool {
	return s.WithMsg
}
