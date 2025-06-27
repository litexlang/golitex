package litex_executor

import (
	"fmt"
	glob "golitex/glob"
)

func (e *Executor) deleteEnvAndRetainMsg() {
	for _, msg := range e.env.Msgs {
		if glob.IsNotImportState() {
			e.env.Parent.AppendMsg2(msg)
		}
	}
	e.env = e.env.Parent
}

func (e *Executor) appendMsg(msg string, str ...any) {
	e.env.Msgs = append(e.env.Msgs, fmt.Sprintf(msg, str...))
}

func (e *Executor) appendNewMsgAtBegin(msg string, str ...any) {
	e.env.Msgs = append([]string{fmt.Sprintf(msg, str...)}, e.env.Msgs...)
}

func (e *Executor) appendWarningMsg(msg string, str ...any) {
	e.env.Msgs = append(e.env.Msgs, fmt.Sprintf(`warning: %s`, fmt.Sprintf(msg, str...)))
}

func (e *Executor) appendInternalWarningMsg(msg string, str ...any) {
	e.env.Msgs = append(e.env.Msgs, glob.InternalWarningMsg(msg, str...))
}

// func (e *Executor) appendMsg(msg string, str ...any) {
// 	if !glob.IsImportState() {
// 		e.env.Msgs = append(e.env.Msgs, fmt.Sprintf(msg, str...))
// 	}
// }
