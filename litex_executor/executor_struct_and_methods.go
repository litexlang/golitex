package litexexecutor

import (
	"fmt"
	mem "golitex/litex_memory"
)

type ExecOutput uint8

const (
	execTrue ExecOutput = iota
	execUnknown
	execError
)

type Executor struct {
	env         *mem.Env
	message     []string
	output      ExecOutput
	searchRound uint8
}

func newExecutor() *Executor {
	return &Executor{env: mem.NewEnv(), message: []string{}, output: execError, searchRound: 0}
}

func (e *Executor) roundAddOne() {
	e.searchRound++
}

func (e *Executor) clear() {
	e.message = []string{}
	e.output = execError
	e.searchRound = 0
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
	return e.output == execTrue
}

func (e *Executor) round1() bool {
	return e.searchRound == 1
}

func (e *Executor) roundMinusOne() {
	e.searchRound--
}

func (e *Executor) success(format string, args ...any) {
	message := fmt.Sprintf(format, args...) // 使用 fmt.Sprintf 格式化字符串
	e.message = append(e.message, message)
	e.output = execTrue
}

func (e *Executor) unknown(format string, args ...any) {
	message := fmt.Sprintf(format, args...)
	e.message = append(e.message, message)
	e.output = execUnknown
}

func (e *Executor) printlnOutputMessage() {
	if e.output == execTrue {
		fmt.Println("True")
	} else if e.output == execUnknown {
		fmt.Println("Unknown")
	} else if e.output == execError {
		fmt.Println("Error")
	}

	for _, msg := range e.message {
		fmt.Println(msg)
	}
}
