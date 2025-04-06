package litexsys

import (
	"fmt"
	"testing"
)

func TestRunFile(t *testing.T) {
	msg, err := ExecFileReturnString("../litex_code_examples/litex_as_regex_matcher.lix")
	if err != nil {
		t.Errorf(err.Error())
	}
	fmt.Println(msg)
}
