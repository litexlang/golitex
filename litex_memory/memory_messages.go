package litexmemory

import (
	parser "golitex/litex_parser"
	"strings"
)

func (fact *StoredFuncFact) String(atom parser.FcAtom) string {
	var builder strings.Builder

	if !fact.IsTrue {
		builder.WriteString("not")
	}

	if atom.PkgName == "" && parser.IsBuiltinSymbol(atom.OptName) {
		builder.WriteString(fact.Params[0].String())
		builder.WriteByte(' ')
		builder.WriteString(atom.OptName)
		builder.WriteByte(' ')
		builder.WriteString(fact.Params[1].String())
		return builder.String()
	}

	builder.WriteString(parser.KeywordDollar)
	builder.WriteString(atom.String())
	builder.WriteByte('(')
	builder.WriteString(parser.FcSliceString(&fact.Params))
	builder.WriteByte(')')

	return builder.String()
}

func (fact *StoredCondFuncFact) String(atom parser.FcAtom) string {
	return fact.Fact.String()
}
