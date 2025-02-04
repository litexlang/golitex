package parser

import "sort"

var BuiltinSyms = map[string]string{
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
	"\\": "\\",
	"?":  "?",
}

func isBuiltinRelationalOperator(op string) bool {
	return op == "<" || op == ">" || op == "<=" || op == ">=" || op == "=" || op == "==" || op == "!="
}

func putBuiltinIntoKeywords() *map[string]string {
	var Keywords = map[string]string{
		"concept":     "concept", // 用在两个地方：声明；作为property判定一个东西是不是特定concept
		"inherit":     "inherit", // 用在两个地方：声明；作为property判定一个东西是不是特定type
		"type_member": "type_member",
		"member":      "member",
		"property":    "property",
		"if":          "if",
		"then":        "then",
		"forall":      "forall",
		"exist":       "exist",
		"have":        "have",
		"var":         "var",
		"type":        "type",
		"fn":          "fn",
		"pub":         "pub",
		"know":        "know",
		"claim":       "claim",
		"proof":       "proof",
		"import":      "import",
		"package":     "package",
		"not":         "not",
		"is":          "is",
		"use":         "use",
		"impl":        "impl",
		"any":         "any",
		"as":          "as",
	}

	for k, v := range BuiltinSyms {
		Keywords[v] = k
	}

	return &Keywords
}

var Keywords map[string]string = *putBuiltinIntoKeywords()

var sortedSymbols []string = sortKeywordSymbols()

// 初始化排序后的符号列表
func sortKeywordSymbols() []string {
	symbols := make([]string, 0, len(BuiltinSyms))
	for k := range BuiltinSyms {
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
