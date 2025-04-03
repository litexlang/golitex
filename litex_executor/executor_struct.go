package litexexecutor

import (
	env "golitex/litex_env"
)

type Executor struct {
	env *env.Env
	// parent  *Executor
	// msgs   []string
	// output ExecOutput
}

func NewExecutor(curEnv *env.Env) *Executor {
	if curEnv == nil {
		return &Executor{env: env.NewEnv(nil, nil)}
	} else {
		return &Executor{env: curEnv}
	}
}

func (e *Executor) newEnv() {
	e.env = env.NewEnv(e.env, nil)
}

func (e *Executor) deleteEnvAndRetainMsg() {
	for _, msg := range e.env.Msgs {
		e.env.Parent.NewMsg(msg)
	}
	e.env = e.env.Parent
}

func (e *Executor) clearMsgAndOutput() {
	e.env.Msgs = []string{}
}

func (e *Executor) getMsgs() []string {
	return e.env.Msgs
}
