package litexexecutor

import (
	env "golitex/litex_env"
)

type ExecOutput uint8

const (
	execTrue ExecOutput = iota
	execUnknown
	execError
)

type Executor struct {
	env *env.Env
	// parent  *Executor
	// msgs   []string
	output ExecOutput
}

func newExecutor(curEnv *env.Env) *Executor {
	if curEnv == nil {
		return &Executor{env: env.NewEnv(nil, nil), output: execUnknown}
	} else {
		return &Executor{env: curEnv, output: execUnknown}
	}
}

func (e *Executor) newEnv() {
	e.env = env.NewEnv(e.env, nil)
}

func (e *Executor) deleteEnv() {
	// e.env.Parent.Msgs = append(e.env.Parent.Msgs, e.env.Msgs...)
	e.env = e.env.Parent
}

func (e *Executor) clearMsgAndOutput() {
	e.env.Msgs = []string{}
	e.output = execUnknown
}

func (e *Executor) true() bool {
	return e.output == execTrue
}

func (e *Executor) getMsgs() []string {
	return e.env.Msgs
}
