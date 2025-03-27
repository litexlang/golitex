package litexmemory

import (
	msg "golitex/litex_messages"
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
	var builder strings.Builder

	builder.WriteString("when:\n")
	for _, condFact := range *fact.CondFacts {
		builder.WriteString(msg.LineHead4Indents(condFact.String(), 1))
		builder.WriteByte('\n')
	}

	newFact := &StoredFuncFact{fact.IsTrue, fact.Params}
	builder.WriteString("    then:\n")
	builder.WriteString(msg.LineHead4Indents(newFact.String(atom), 2))
	builder.WriteByte('\n')

	return builder.String()
}
