package litexexecutor

func (e *Executor) newMsgEnd(msg string) {
	e.env.Msgs = append(e.env.Msgs, msg)
}
