package parser

var Keywords = map[string]string{
	"concept":  "concept",
	"property": "property",
	"if":       "if",
	"opt":      "opt",
	"fn":       "fn",
	"local":    "local",
	"exist":    "exist",
	"let":      "let",
	"pub":      "pub",
	"know":     "know",
	"claim":    "claim",
	"prove":    "prove",
	"import":   "import",
}

var KeyChars = map[string]string{
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
}
