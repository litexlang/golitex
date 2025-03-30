package litexverifier

import (
	parser "golitex/litex_parser"
)

func (ver *Verifier) UniFact(stmt *parser.UniFactStmt) (bool, error) {
	return false, nil
}
