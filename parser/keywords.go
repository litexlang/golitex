package parser

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
}

// if inputString starting from position start is KeywordSymbols
func isKeywordSymbol(inputString string, start int) bool {
	for k, v := range KeywordSymbols {
		if start+len(k) <= len(inputString) && inputString[start:start+len(k)] == v {
			return true
		}
	}
	return false
}
