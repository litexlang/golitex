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

// TODO: 还没有和type联动起来
var CustomizableOperators = map[string]string{
	"/":              "__div__",
	"+":              "__add__",
	"-":              "__sub__",
	"*":              "__mul__",
	"^":              "__xor__",
	"<":              "__lt__",
	">":              "__gt__",
	"!":              "__not__",
	"|":              "__or__",
	"&":              "__and__",
	"~":              "__invert__",
	"++":             "__add_add__",
	"--":             "__sub_sub__",
	"&&":             "__and__",
	"||":             "__or_or__",
	"==":             "__eq_eq__",
	"!=":             "__ne__",
	"**":             "__pow__",
	"<=":             "__lt_eq__",
	">=":             "__gt_eq__",
	"\\in":           "__in__",
	"\\has":          "__has__",
	"\\union":        "__union__",
	"\\intersection": "__intersection__",
	"\\subset_eq":    "__subset_eq__",
	"\\supset_eq":    "__supset_eq__",
	"\\subset":       "__subset__",
	"\\supset":       "__supset__",
	"->":             "__sub_gt__",
	"=>":             "__eq_gt__",
}

func isBuiltinRelationalOperator(op string) bool {
	return op == "<" || op == ">" || op == "<=" || op == ">=" || op == "=" || op == "==" || op == "!="
}

func putBuiltinIntoKeywords() *map[string]string {
	var Keywords = map[string]string{
		"set_struct":             "set_struct",
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
		"ret":                    "ret",

		// Syntax and Semantics Sugar
		// I should give user keyword commutative and associative otherwise Litex can not verify (v1 + v2)@k = v2@k + v1@k even we we know (v1 + v2)@k = v1@k + v2@k
		"commutative": "commutative",
		"associative": "associative",

		// The followings are builtin types.
		"Nat":   "Nat",   // e.g. 0
		"Int":   "Int",   // e.g. -1
		"Float": "Float", // e.g. -1.1
		"Set":   "Set",   // e.g. to_set(AnyType)

		// Builtin functions

		// Set is a special type in Litex. The only difference between set and user-defined type is: types can be transformed into a set. If 2 type do manipulate, I by default cancel all the structures that have, and view them as plain sets. An instance of a type can be passed here and there. Users can define their own union or intersection operator. 即如果两个type要做集合运算，他们上面的结构自动消失变成纯集合（这是最关键观察.另一大重要观察是type =set+structure）。同时我可能还要设计一个额外的语法，让一个给定的集合上面可以绑定结构，让它变成type。set不能出现在的parameter list的 var-type pair 里，不能出现在 type parameters，它是纯粹的实例，只不过绑定了in这个Operator。这个set关键词解决了type的用途重载的问题：本来集合只能被表示成type，而type又是有结构的，即type同时有结构+集合两重意思。如果a TypeName，则a自动满足 a in make_set[TypeName]。只有变量能被运算，type不能。把type变成set后，这个东西才能被运算
		"make_set": "make_set", // e.g. make_set[TypeName]
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
