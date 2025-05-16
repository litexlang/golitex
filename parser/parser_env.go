package litex_parser

type ParserEnv struct {
	PkgManagementMap map[string]string
}

func NewParserEnv() *ParserEnv {
	return &ParserEnv{PkgManagementMap: make(map[string]string)}
}
