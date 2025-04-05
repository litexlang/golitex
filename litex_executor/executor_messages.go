package litexexecutor

func (e *Executor) appendNewMsg(msg string) {
	e.env.Msgs = append(e.env.Msgs, msg)
}
