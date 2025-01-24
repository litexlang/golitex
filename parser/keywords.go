package parser

import "sort"

var Keywords = map[string]string{
	"concept":        "concept",
	"property":       "property",
	"if":             "if",
	"fn":             "fn",
	"local":          "local",
	"exist":          "exist",
	"let":            "let",
	"pub":            "pub",
	"know":           "know",
	"claim":          "claim",
	"prove":          "prove",
	"import":         "import",
	"package":        "package",
	"exist_property": "exist_property",
	"return":         "return",
}

var KeywordSymbols = map[string]string{
	":":  ":",
	"[":  "[",
	"]":  "]",
	"(":  "(",
	")":  ")",
	",":  ",",
	"$":  "$",
	"=":  "=",
	"/":  "/",
	"+":  "+",
	"-":  "-",
	"*":  "*",
	"^":  "^",
	"<":  "<",
	">":  ">",
	"!":  "!",
	"|":  "|",
	"~":  "~",
	"&":  "&",
	".":  ".",
	"::": "::",
	"++": "++",
	"--": "--",
	"&&": "&&",
	"||": "||",
	"==": "==",
	"!=": "!=",
}
var sortedSymbols []string = sortKeywordSymbols()

// 初始化排序后的符号列表
func sortKeywordSymbols() []string {
	symbols := make([]string, 0, len(KeywordSymbols))
	for k := range KeywordSymbols {
		symbols = append(symbols, k)
	}
	sort.Slice(symbols, func(i, j int) bool {
		return len(symbols[i]) > len(symbols[j])
	})
	return symbols
}

// 缓存排序后的符号列表

// 如果输入字符串从起始位置开始是符号，则返回该符号
func getKeywordSymbol(inputString string, start int) string {
	for _, k := range sortedSymbols {
		end := start + len(k)
		if end <= len(inputString) {
			match := true
			for i := 0; i < len(k); i++ {
				if inputString[start+i] != k[i] {
					match = false
					break
				}
			}
			if match {
				return k
			}
		}
	}
	return ""
}
