package litexexecutor

import (
	"fmt"
	env "golitex/litexenv"
	parser "golitex/litexparser"
	"testing"
)

func TestStoreNewVar(t *testing.T) {
	code := `var a G`
	statements, err := parser.ParseSourceCode(code)
	if err != nil {
		t.Fatal(err)
	}
	env := env.NewEnv()
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
