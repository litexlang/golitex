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

// verifier 的方法的命名方式：factType+?UseWhatMemToVerify+?atEnv, 比如 RelaFactSpecAtEnv 就是说 证明 relaFact, 方法是用SpecFact，在当前环境里.
package litex_verifier

import (
	"fmt"
	env "golitex/environment"
	glob "golitex/glob"
)

type Verifier struct {
	env *env.Env
}

func NewVerifier(curEnv *env.Env) *Verifier {
	if curEnv == nil {
		return &Verifier{env: env.NewEnv(nil)}
	} else {
		return &Verifier{env: curEnv}
	}
}

func (ver *Verifier) newEnv(parent *env.Env) {
	newEnv := env.NewEnv(parent)
	ver.env = newEnv
}

func (ver *Verifier) deleteEnvAndRetainMsg() error {
	if ver.env.Parent != nil {
		for _, msg := range ver.env.Msgs {
			if glob.IsNotImportDirStmt() {
				ver.env.Parent.AppendMsg(msg)
			}
		}
		ver.env = ver.env.Parent
		return nil
	} else {
		return fmt.Errorf("parent env does not exist")
	}
}
