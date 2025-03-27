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

	for _, msg := range *e.message {
		fmt.Println(msg)
	}
}
