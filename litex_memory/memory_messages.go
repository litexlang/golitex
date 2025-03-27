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
