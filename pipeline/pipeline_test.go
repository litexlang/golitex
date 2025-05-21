package litex_pipeline

import (
	"fmt"
	"testing"
)

func TestREPL(t *testing.T) {
	RunREPL()
}

func TestExecuteCodeAndReturnMessage(t *testing.T) {
	code := `
obj a N
	`
	msg, signal, err := ExecuteCodeAndReturnMessage(code)
	if err != nil {
		t.Fatalf("ExecuteCodeAndReturnMessage failed: %v", err)
	}
	fmt.Println(msg)
	fmt.Println(signal)
}
