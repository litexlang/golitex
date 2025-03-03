package litexexecutor

import (
	mem "golitex/litex_memory"
)

const (
	ExecTrue ExecOutput = iota
	ExecUnknown
	ExecError
)

type ExecOutput uint8

type Executor struct {
	env     *mem.Env
	message []string
	output  ExecOutput
}

func (e *Executor) success(message string) {
	e.message = append(e.message, message)
	e.output = ExecTrue
}
