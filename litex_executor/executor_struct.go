package litexexecutor

import (
	env "golitex/litex_env"
	verifier "golitex/litex_verifier"
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
	msgSliceSlice []string
	output        ExecOutput
}

func newExecutor(curEnv *env.Env) *Executor {
	if curEnv == nil {
		return &Executor{env: env.NewEnv(nil, nil), msgSliceSlice: []string{}, output: execUnknown}
	} else {
		return &Executor{env: curEnv, msgSliceSlice: []string{}, output: execUnknown}
	}
}

func (e *Executor) newEnv() {
	e.env = env.NewEnv(e.env, nil)
}

func (e *Executor) deleteEnv() {
	e.env = e.env.Parent
}

func (e *Executor) clearMsgAndOutput() {
	e.msgSliceSlice = []string{}
	e.output = execUnknown
}

func (e *Executor) true() bool {
	return e.output == execTrue
}

func (e *Executor) readFromVerifier(readFrom *verifier.Verifier, putMsgReverseOrder bool) {
	switch readFrom.Output {
	case verifier.VerifierTrue:
		e.output = execTrue
	case verifier.VerifierError:
		e.output = execError
	case verifier.VerifierUnknown:
		e.output = execUnknown
	}

	// e.message = readFrom.Message
	// slices.Reverse(*readFrom.Message)
	// *e.message = append(*e.message, strings.Join(*readFrom.Message, "\n"))
	e.msgSliceSlice = append(e.msgSliceSlice, *readFrom.Message...)
}
