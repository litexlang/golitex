package litexexecutor

import (
	"fmt"
	mem "golitex/litex_memory"
)

type ExecOutput uint8

const (
	ExecTrue ExecOutput = iota
	ExecUnknown
	ExecError
)

type Executor struct {
	env         *mem.Env
	message     []string
	output      ExecOutput
	searchRound int8
}

func newExecutor() *Executor {
	return &Executor{env: mem.NewEnv(), message: []string{}, output: ExecError, searchRound: 0}
}

func (e *Executor) clear() {
	e.message = []string{}
	e.output = ExecError
	e.searchRound = -1
}

func (e *Executor) newEnv() {
	newEnv := mem.NewEnv()
	newEnv.Parent = e.env
	e.env = newEnv
}

func (e *Executor) deleteEnv() {
	e.env = e.env.Parent
}

func (e *Executor) true() bool {
	return e.output == ExecTrue
}

func (e *Executor) round0() bool {
	return e.searchRound == 0
}

func (e *Executor) roundMinusOne() {
	e.searchRound--
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

func (e *Executor) printlnOutputMessage() {
	if e.output == ExecTrue {
		fmt.Println("True")
	} else if e.output == ExecUnknown {
		fmt.Println("Unknown")
	} else if e.output == ExecError {
		fmt.Println("Error")
	}

	for _, msg := range e.message {
		fmt.Println(msg)
	}
}
