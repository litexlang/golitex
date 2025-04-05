package litexexecutor

import (
	env "golitex/litex_env"
)

type Executor struct {
	env *env.Env
}

// 如果你传入的是nil，那默认这个exec里的env的curPkg是""
func NewExecutor(curEnv *env.Env) *Executor {
	if curEnv == nil {
		return &Executor{env: env.NewEnv(nil, nil, "")}
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
