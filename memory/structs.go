package memory

import (
	"golitex/parser"
)

type Fc = parser.Fc
type PropertyType = parser.PropertyType

type SpecificFactsAboutTheSameOperatorName []struct{ propertyType PropertyType }

type MemSpecificFact struct {
	fact parser.NotFactStmt
}

type MemForallFact struct{}
