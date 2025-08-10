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

type Ver_State struct {
	Round   uint8
	WithMsg bool
	ReqOk   bool
}

func (s *Ver_State) addRound() {
	s.Round++
}

func (s *Ver_State) toNoMsg() {
	s.WithMsg = false
}

func (s *Ver_State) toReqOk() {
	s.ReqOk = true
}

func (s *Ver_State) isFinalRound() bool {
	return s.Round >= 2 // return s.Round == 2
}

func (s *Ver_State) ToFinalRound() *Ver_State {
	return &Ver_State{
		Round:   2,
		WithMsg: s.WithMsg,
		ReqOk:   s.ReqOk,
	}
}

func (s *Ver_State) String() string {
	if s.WithMsg {
		return fmt.Sprintf("Round %d with msg", s.Round)
	} else {
		return fmt.Sprintf("Round %d without msg", s.Round)
	}
}
