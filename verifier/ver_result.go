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

type VerRet interface {
	verRet()
	isTrue() bool
	isUnknown() bool
	isErr() bool
}

func (v *VerTrue) verRet()
func (v *VerTrue) isTrue() bool    { return true }
func (v *VerTrue) isUnknown() bool { return false }
func (v *VerTrue) isErr() bool     { return false }

func (v *VerErr) verRet()
func (v *VerErr) isTrue() bool    { return false }
func (v *VerErr) isUnknown() bool { return false }
func (v *VerErr) isErr() bool     { return true }

func (v *VerUnknown) verRet()
func (v *VerUnknown) isTrue() bool    { return false }
func (v *VerUnknown) isUnknown() bool { return true }
func (v *VerUnknown) isErr() bool     { return false }

type VerTrue struct {
	Msg []string
}

type VerUnknown struct {
	Msg []string
}

type VerErr struct {
	Msg []string
}
