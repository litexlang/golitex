package litexexecutor

import "fmt"

func (e *Executor) printlnExecOutput() {
	if e.output == execTrue {
		fmt.Println("True")
	} else if e.output == execUnknown {
		fmt.Println("Unknown")
	} else if e.output == execError {
		fmt.Println("Error")
	}

	for _, msg := range e.env.Msgs {
		fmt.Println(msg)
	}
}

func (e *Executor) newMessage(msg string) {
	e.env.Msgs = append(e.env.Msgs, msg)
}

func (e *Executor) newMsgAt0(msg string) {
	e.env.Msgs = append([]string{msg}, e.env.Msgs...)
}
