package litex_global

var SuperFunctionsSet map[string]struct{} = map[string]struct{}{
	KeywordUnion:     {},
	KeywordIntersect: {},
}

func IsSuperFunction(name string) bool {
	_, ok := SuperFunctionsSet[name]
	return ok
}
