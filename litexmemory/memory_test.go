package litexmemory

import (
	parser "golitex/litexparser"
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
h[a](b).g[c](d).t
`
	tokenBlocks, err := parser.ParseSourceCodeGetTokenBlock(code)
	if err != nil {
		t.Fatal(err)
	}

	for _, block := range *tokenBlocks {
		it := block.Header
		// 单独把node拿出来parse可能会有问题：因为我在parse时默认在parse stmt，所以你想要单独parse fc是会出错的。比如parse "h[a](b).g[c](d).t"时，我解释器会往t后面读东西以确定现在在什么位置，但如果 它 单独出现，那t就在最后了，就会 out of range。我这里的implement让 out of range 不可能，但以后不确定
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
