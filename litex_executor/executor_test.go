package litexexecutor

import (
	"fmt"
	memory "golitex/litex_memory"
	parser "golitex/litex_parser"
	"testing"
)

func TestStoreNewVar(t *testing.T) {
	code := `var a G`
	statements, err := parser.ParseSourceCode(code)
	if err != nil {
		t.Fatal(err)
	}
	env := memory.NewEnv()
	for _, topStmt := range *statements {
		value, err := ExecTopLevelStmt(env, &topStmt)
		if err != nil {
			t.Fatal(err)
		}
		fmt.Println(value)
	}

	entry, _ := env.VarMemory.Get("a")
	println(string(entry.Tp.Value.(parser.FcVarTypeStrValue)))
}
