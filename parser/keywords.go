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

var KeywordChars = map[string]string{
	":": ":",
	"[": "[",
	"]": "]",
	"(": "(",
	")": ")",
	",": ",",
	"$": "$",
	"=": "=",
	"/": "/",
	"+": "+",
	"-": "-",
	"*": "*",
	"^": "^",
	"<": "<",
	">": ">",
	"!": "!",
	"|": "|",
	"~": "~",
	"&": "&",
	".": ".", // postfix operator
}
