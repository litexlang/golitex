package litexmemory

import (
	parser "golitex/litex_parser"
)

func (c *PropFactContainer) put(fact parser.SpecFactStmt) error {
	return nil
}

func (c *PropFactContainer) IsKnown(fact parser.SpecFactStmt) (bool, error) {
	return false, nil
}

func CompSpecFactParams(knownFact parser.SpecFactStmt, givenFact parser.SpecFactStmt) int {
	return 0
}
