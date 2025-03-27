package litexexecutor

import (
	"fmt"
	env "golitex/litex_env"
	verifyPkg "golitex/litex_verifier"
)

type ExecOutput uint8

const (
	execTrue ExecOutput = iota
	execUnknown
	execError
)

type Executor struct {
	env     *env.Env
	message *[]string
	output  ExecOutput
}

func newExecutor(curEnv *env.Env) *Executor {
	if curEnv == nil {
		return &Executor{env: env.NewEnv(nil), message: &[]string{}, output: execUnknown}
	} else {
		return &Executor{env: curEnv, message: &[]string{}, output: execUnknown}
	}
}

func (e *Executor) clear() {
	e.message = &[]string{}
	e.output = execUnknown
}

func (e *Executor) true() bool {
	return e.output == execTrue
}

func (e *Executor) success(format string, args ...any) {
	message := fmt.Sprintf(format, args...) // 使用 fmt.Sprintf 格式化字符串
	*e.message = append(*e.message, message)
	e.output = execTrue
}

func (e *Executor) readFromVerifier(readFrom *verifyPkg.Verifier) {
	switch readFrom.Output {
	case verifyPkg.VerifierTrue:
		e.output = execTrue
	case verifyPkg.VerifierError:
		e.output = execError
	case verifyPkg.VerifierUnknown:
		e.output = execUnknown
	}

	e.message = readFrom.Message
}
