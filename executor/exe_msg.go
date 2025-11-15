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

package litex_executor

func (e *Executor) deleteEnv() {
	// Note: Messages are now stored in ExecRet, not in env.Msgs
	// This function is kept for compatibility but does nothing
	e.Env = e.Env.Parent
}

func (e *Executor) deleteEnvAndGiveUpMsgs() {
	e.Env = e.Env.Parent
}
