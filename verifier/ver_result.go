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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import "fmt"

type VerRet struct {
	Ok  bool
	Msg []string
	Err error
}

func (ver *VerRet) newMsg(msg string) *VerRet {
	ver.Msg = append(ver.Msg, msg)
	return ver
}

func (ver *VerRet) IsErr() bool {
	return ver.Err != nil
}

func (ver *VerRet) IsOk() bool {
	return ver.Ok
}

func (ver *VerRet) IsUnknown() bool {
	return !ver.Ok && ver.Err == nil
}

func newErrVerRet(msg string, args ...any) *VerRet {
	return &VerRet{
		Ok:  false,
		Msg: []string{fmt.Sprintf(msg, args...)},
		Err: fmt.Errorf(msg, args...),
	}
}

func newTrueVerRet(msg string, args ...any) *VerRet {
	return &VerRet{
		Ok:  true,
		Msg: []string{fmt.Sprintf(msg, args...)},
		Err: nil,
	}
}

func newUnknownVerRet(msg string, args ...any) *VerRet {
	return &VerRet{
		Ok:  false,
		Msg: []string{fmt.Sprintf(msg, args...)},
		Err: nil,
	}
}
