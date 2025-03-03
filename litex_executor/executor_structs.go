package litexexecutor

import (
	"fmt"
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

func (e *Executor) success(format string, args ...any) {
	message := fmt.Sprintf(format, args...) // 使用 fmt.Sprintf 格式化字符串
	e.message = append(e.message, message)
	e.output = ExecTrue
}

func (e *Executor) unknown(format string, args ...any) {
	message := fmt.Sprintf(format, args...)
	e.message = append(e.message, message)
	e.output = ExecUnknown
}
