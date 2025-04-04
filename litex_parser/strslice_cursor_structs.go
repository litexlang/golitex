package litexparser

import (
	"fmt"
	"strings"
)

type StrSliceCursor struct {
	index int
	slice []string
}

func (p *StrSliceCursor) strAtCurIndexPlus(plusIndex int) string {
	i := p.index + plusIndex

	if i < 0 || i >= len(p.slice) {
		return ""
	} else {
		return p.slice[i]
	}
}

func (p *StrSliceCursor) String() string {
	return strings.Join(p.slice, " ")
}

func (p *StrSliceCursor) getIndex() int {
	return p.index
}

func (p *StrSliceCursor) getSlice() []string {
	return p.slice
}

func (p *StrSliceCursor) currentToken() (string, error) {
	if p.index >= len(p.slice) {
		return "", fmt.Errorf("unexpected end of slice %v", p.slice)
	}
	return p.slice[p.index], nil
}

func (it *StrSliceCursor) testAndSkip(s string) error {
	if it.index >= len(it.slice) {
		return fmt.Errorf("unexpected end of slice %v", it.slice)
	}
	if it.slice[it.index] == s {
		it.index++
		return nil
	}
	return fmt.Errorf("expected '%s', but got '%s'", s, it.slice[it.index])
}

func (it *StrSliceCursor) next() (string, error) {
	if it.index >= len(it.slice) {
		return "", fmt.Errorf("unexpected end of slice %v", it.slice)
	}
	it.index++
	return it.slice[it.index-1], nil
}

func (it *StrSliceCursor) is(s string) bool {
	return it.index < len(it.slice) && it.slice[it.index] == s
}

func (it *StrSliceCursor) isAndSkip(expected string) bool {
	if it.index < len(it.slice) && it.slice[it.index] == expected {
		it.index++
		return true
	} else {
		return false
	}
}

func (it *StrSliceCursor) ExceedEnd() bool {
	return it.index >= len(it.slice)
}

func (it *StrSliceCursor) skip(expected ...string) error {
	if it.index >= len(it.slice) {
		return fmt.Errorf("unexpected end of slice %v", it.slice)
	}

	if len(expected) == 0 {
		it.index++
		return nil
	}

	if it.slice[it.index] == expected[0] {
		it.index++
	} else {
		return fmt.Errorf("expected '%s', but got '%s'", expected[0], it.slice[it.index])
	}

	return nil
}

func (it *StrSliceCursor) curTokenBeginWithNumber() bool {
	if it.index >= len(it.slice) {
		return false
	}

	if it.slice[it.index][0] >= '0' && it.slice[it.index][0] <= '9' {
		return true
	} else {
		return false
	}
}

type parserErr struct {
	previous error
	parser   *StrSliceCursor
}

func (e *parserErr) Error() string {
	curTok, err := e.parser.currentToken()
	if err != nil {
		return fmt.Sprintf("error at %s, column %d: %s", e.parser.String(), e.parser.getIndex(), e.previous.Error())
	} else {
		return fmt.Sprintf("error at %s, column %d, at '%s': %s", e.parser.String(), e.parser.getIndex(), curTok, e.previous.Error())
	}
}
