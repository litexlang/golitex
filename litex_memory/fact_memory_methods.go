package litexmemory

import (
	parser "golitex/litex_parser"
)

func (c *KnownSpecPropFactContainer) put(fact parser.SpecFactStmt) error {
	c.facts = append(c.facts, fact)

	return nil
}

func (c *KnownSpecPropFactContainer) match(fact parser.SpecFactStmt) (bool, error) {
	for _, knownFact := range c.facts {
		comp := parser.CompareParamsInSpecFact(knownFact, fact)
		if comp == 0 {
			return true, nil
		}
	}

	return false, nil
}
