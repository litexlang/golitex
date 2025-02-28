package litexmemory

import (
	parser "golitex/litex_parser"
)

func (c *KnownSpecPropFactContainer) put(fact parser.SpecFactStmt) error {
	c.facts = append(c.facts, fact)

	return nil
}

func (c *KnownSpecPropFactContainer) IsKnown(fact parser.SpecFactStmt) (bool, error) {
	for _, knownFact := range c.facts {
		comp := CompSpecFactParams(knownFact, fact)
		if comp == 0 {
			return true, nil
		}
	}

	return false, nil
}

func CompSpecFactParams(knownFact parser.SpecFactStmt, givenFact parser.SpecFactStmt) int {
	return 0
}
