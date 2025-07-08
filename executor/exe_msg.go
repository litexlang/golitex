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

package litex_executor

import (
	"fmt"
	glob "golitex/glob"
)

func (e *Executor) deleteEnvAndRetainMsg() {
	for _, msg := range e.env.Msgs {
		if glob.IsNotImportDirStmt() {
			e.env.Parent.AppendMsg(msg)
		}
	}
	e.env = e.env.Parent
}

func (e *Executor) appendMsg(msg string) {
	e.env.Msgs = append(e.env.Msgs, msg)
}

func (e *Executor) appendNewMsgAtBegin(msg string, str ...any) {
	e.env.Msgs = append([]string{fmt.Sprintf(msg, str...)}, e.env.Msgs...)
}

func (e *Executor) appendWarningMsg(msg string, str ...any) {
	e.env.Msgs = append(e.env.Msgs, fmt.Sprintf(`warning: %s`, fmt.Sprintf(msg, str...)))
}

func (e *Executor) ClearMsgs() {
	e.env.Msgs = []string{}
}
