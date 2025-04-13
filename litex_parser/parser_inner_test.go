package litex_parser

import (
	"fmt"
	ast "golitex/litex_ast"
	"log"
	"os"
	"testing"
	"time"
)

func readFile(filePath string) string {
	content, err := os.ReadFile(filePath)
	if err != nil {
		panic(err)
	}
	return string(content)
}

var code = readFile("../litex_code_examples/parser_test/def.lix")

func TestLexTimeParseTime(t *testing.T) {

	veryStart := time.Now()

	start := time.Now()
	preprocessedCodeLines, err := preprocessSourceCode(code)
	if err != nil {
		panic(err)
	}
	preprocessTime := time.Since(start)

	blocks, err := makeTokenBlocks(preprocessedCodeLines)

	if err != nil {
		panic(err)
	}

	tokenizeBlockTime := time.Since(start)

	start = time.Now()
	ret := []ast.TopStmt{}
	for _, block := range blocks {
		cur, err := block.TopStmt()
		if err != nil {
			log.Fatalln(err)
		}
		ret = append(ret, *cur)
	}
	parseTime := time.Since(start)

	allTime := time.Since(veryStart)

	fmt.Println(ret)

	// preprocess 47.291µs
	// getStrBlock 11.25µs
	// tokenize 74.708µs
	// parse 89.041µs
	fmt.Printf("preprocess %v\nmakeBlock %v\nparse %v\n", preprocessTime, tokenizeBlockTime, parseTime)
	fmt.Printf("all %v", allTime)
}
