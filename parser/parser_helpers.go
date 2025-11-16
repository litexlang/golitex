package litex_parser

import (
	"fmt"
	glob "golitex/glob"
)

// expectAndSkipCommaOr checks the next token after an item:
// - if it's a comma, it skips it and returns (done=false, nil)
// - if it's the expected end token, it returns (done=true, nil)
// - otherwise, returns an error
func (tb *tokenBlock) expectAndSkipCommaOr(endToken string) (bool, error) {
	if tb.header.is(glob.KeySymbolComma) {
		tb.header.skip(glob.KeySymbolComma)
		return false, nil
	}
	if !tb.header.is(endToken) {
		return false, tbErr(fmt.Errorf("expected '%s' but got '%s'", endToken, tb.header.strAtCurIndexPlus(0)), tb)
	}
	return true, nil
}
