package memory

import (
	"golitex/parser"
	"testing"
)

func TestGetMemKey(t *testing.T) {
	code := `
h[a](b).g[c](d).t is red
f(t) is red
`
	statements, err := parser.ParseSourceCode(code)

	if err != nil {
		t.Fatal(err)
	}

	keys := []string{}
	for _, topStatement := range *statements {
		statement := topStatement.Stmt
		stmt := statement.(*parser.FuncPtyStmt)
		propertyFc := stmt.Fc.(*parser.CalledFcFnRetValue)
		fc := propertyFc.VarParams[0]
		memKey, err := getMemoryKey(fc)
		if err != nil {
			t.Fatal(err)
		}

		keys = append(keys, memKey)
	}

	for _, key := range keys {
		t.Log(key)
	}
}

func TestGetMemKey2(t *testing.T) {
	code := `
f(t)
f(h[a](b).g[c](d).t)
`
	tokenBlocks, err := parser.ParseSourceCodeGetTokenBlock(code)
	if err != nil {
		t.Fatal(err)
	}

	for _, block := range *tokenBlocks {
		it := block.Header
		fc, err := it.ParseFcExpr()
		if err != nil {
			t.Fatal(err)
		}
		memKey, err := getMemoryKey(fc)
		if err != nil {
			t.Fatal(err)
		}
		t.Log(memKey)
	}
}
