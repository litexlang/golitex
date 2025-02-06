package memory

import (
	"fmt"
	"golitex/parser"
	"testing"
)

func TestGetMemKey(t *testing.T) {
	code := `
f()
`
	tokenBlocks, err := parser.GetSourceCodeTokenBlock(code)
	if err != nil {
		t.Fatal(err)
	}

	keys := []string{}
	for _, block := range *tokenBlocks {
		it := (block.Header)
		fc, err := it.ParseFcExpr()
		if err != nil {
			t.Fatal(err)
		}
		key, err := getMemoryKey(fc)
		if err != nil {
			t.Fatal(err)
		}
		keys = append(keys, key)
	}

	for _, key := range keys {
		fmt.Println(key)
	}
}
