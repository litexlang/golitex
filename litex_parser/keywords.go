package litexparser

import "sort"

var BuiltinSyms = map[string]string{
	":":     ":",
	"[":     "[",
	"]":     "]",
	"(":     "(",
	")":     ")",
	",":     ",",
	"$":     "$",
	"=":     "=",
	"/":     "/",
	"+":     "+",
	"-":     "-",
	"*":     "*",
	"^":     "^",
	"<":     "<",
	">":     ">",
	"!":     "!",
	"|":     "|",
	"~":     "~",
	"&":     "&",
	".":     ".",
	"::":    "::",
	"++":    "++",
	"--":    "--",
	"&&":    "&&",
	"||":    "||",
	"==":    "==",
	"!=":    "!=",
	"\\":    "\\",
	"?":     "?",
	"**":    "**",
	"\"":    "\"",
	"'":     "'",
	"`":     "`",
	"=>":    "=>",
	";":     ";",
	"{":     "{",
	"}":     "}",
	"\\[":   "\\[",
	"\\]":   "\\]",
	"#":     "#",
	"\\in":  "\\in",
	"\\has": "\\has",
	"@":     "@", // v@n represents v[n]
}

var CustomizableOperators = map[string]string{
	"/":     "__div__",
	"+":     "__add__",
	"-":     "__sub__",
	"*":     "__mul__",
	"^":     "__xor__",
	"<":     "__lt__",
	">":     "__gt__",
	"!":     "__not__",
	"|":     "__or__",
	"&":     "__and__",
	"~":     "__invert__",
	"++":    "__add_add__",
	"--":    "__sub_sub__",
	"&&":    "__and__",
	"||":    "__or_or__",
	"==":    "__eq_eq__",
	"!=":    "__ne__",
	"**":    "__pow__",
	"<=":    "__lt_eq__",
	">=":    "__gt_eq__",
	"\\in":  "__in__",
	"\\has": "__has__",
}

func isBuiltinRelationalOperator(op string) bool {
	return op == "<" || op == ">" || op == "<=" || op == ">=" || op == "=" || op == "==" || op == "!="
}

func putBuiltinIntoKeywords() *map[string]string {
	var Keywords = map[string]string{
		"concept":                "concept",
		"type":                   "type",
		"type_member":            "type_member",
		"instance_member":        "instance_member",
		"forall":                 "forall",
		"cond":                   "cond",
		"then":                   "then",
		"var":                    "var",
		"fn":                     "fn",
		"prop":                   "prop",
		"know":                   "know",
		"exist":                  "exist",
		"have":                   "have",
		"claim":                  "claim",
		"prove":                  "prove",
		"pub":                    "pub",
		"import":                 "import",
		"package":                "package",
		"not":                    "not",
		"is":                     "is",
		"impl":                   "impl",
		"any":                    "any",
		"as":                     "as",
		"axiom":                  "axiom",
		"prove_by_contradiction": "prove_by_contradiction",
		"thm":                    "thm",
		"when":                   "when",
		// I should give user keyword commutative and associative otherwise Litex can not verify (v1 + v2)@k = v2@k + v1@k even we we know (v1 + v2)@k = v1@k + v2@k
		"commutative": "commutative",
		"associative": "associative",
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
