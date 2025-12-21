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

// verifier 的方法的命名方式：factType+?UseWhatMemToVerify+?atEnv, 比如 RelaFactSpecAtEnv 就是说 证明 relaFact, 方法是用SpecFact，在当前环境里.
package litex_executor

import (
	env "golitex/environment"
)

type Verifier struct {
	Env *env.EnvMgr
}

func NewVerifier(envMgr *env.EnvMgr) *Verifier {
	if envMgr == nil {
		return &Verifier{Env: env.NewEnvMgr(nil)}
	} else {
		return &Verifier{Env: envMgr}
	}
}

func (ver *Verifier) newEnv() *env.EnvMgr {
	return ver.Env.NewEnv()
}

func (ver *Verifier) deleteEnv() error {
	ver.Env.DeleteEnv()
	return nil
}
