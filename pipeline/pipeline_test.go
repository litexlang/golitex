package litex_pipeline

import (
	"fmt"
	"os"
	"testing"

	glob "golitex/glob"
)

func TestExecuteCodeAndReturnMessage(t *testing.T) {
	code := readFile("../examples/test_codes/tmp.lix")
	msg, signal, err := ExecuteCodeAndReturnMessage(code)
	if err != nil {
		t.Errorf("Error: %v", err)
	}
	if signal != glob.SysSignalTrue {
		t.Errorf("Expected signal to be true, got %v", signal)
	}
	fmt.Println(msg)
}

func readFile(filePath string) string {
	content, err := os.ReadFile(filePath)
	if err != nil {
		panic(err)
	}
	return string(content)
}
