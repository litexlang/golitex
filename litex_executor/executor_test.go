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
	executor := Executor{env, []string{}, ExecTrue}
	for _, topStmt := range *statements {
		err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			t.Fatal(err)
		}
		fmt.Println(executor.output)
		fmt.Println(executor.message)
	}

	entry, _ := env.VarMemory.Get("a")
	println(string(entry.Tp.Value.(parser.FcVarTypeStrValue)))
}

func TestKnow(t *testing.T) {
	code := `know $p(a)`
	statements, err := parser.ParseSourceCode(code)
	if err != nil {
		t.Fatal(err)
	}
	env := memory.NewEnv()
	executor := Executor{env, []string{}, ExecTrue}
	for _, topStmt := range *statements {
		err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			t.Fatal(err)
		}
		fmt.Println(executor.output)
		fmt.Println(executor.message)
	}
}

func TestVerifier(t *testing.T) {
	code := `know $p(a)`
	statements, err := parser.ParseSourceCode(code)
	if err != nil {
		t.Fatal(err)
	}
	env := memory.NewEnv()
	executor := Executor{env, []string{}, ExecTrue}
	for _, topStmt := range *statements {
		err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			t.Fatal(err)
		}
		fmt.Println(executor.output)
		fmt.Println(executor.message)
	}

	testCodes := "$p(b)\n$p(a)"
	testStatements, err := parser.ParseSourceCode(testCodes)
	if err != nil {
		t.Fatal(err)
	}

	for _, testCode := range *testStatements {
		err := executor.TopLevelStmt(&testCode)
		if err != nil {
			t.Fatal(err)
		}
		executor.println()
	}
}
