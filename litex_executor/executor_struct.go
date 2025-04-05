package litexexecutor

import (
	env "golitex/litex_env"
)

type Executor struct {
	env *env.Env
	// curPkg string
	// parent  *Executor
	// msgs   []string
	// output ExecOutput
}

func NewExecutor(curEnv *env.Env, curPkg string) *Executor {
	if curEnv == nil {
		return &Executor{env: env.NewEnv(nil, nil, curPkg)}
	} else {
		return &Executor{env: curEnv}
	}
}

func (e *Executor) newEnv(curPkg string) {
	e.env = env.NewEnv(e.env, nil, curPkg)
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
