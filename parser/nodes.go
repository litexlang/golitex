package parser

import "fmt"

type Parser struct {
	index int
	slice []string
}

func (p *Parser) currentToken() (string, error) {
	if p.index >= len(p.slice) {
		return "", fmt.Errorf("unexpected end of slice %v", p.slice)
	}
	return p.slice[p.index], nil
}

func (it *Parser) testAndSkip(s string) error {
	if it.index >= len(it.slice) {
		return fmt.Errorf("unexpected end of slice %v", it.slice)
	}
	if it.slice[it.index] == s {
		it.index++
		return nil
	}
	return fmt.Errorf("expected '%s', but got '%s'", s, it.slice[it.index])
}

func (it *Parser) next() (string, error) {
	if it.index >= len(it.slice) {
		return "", fmt.Errorf("unexpected end of slice %v", it.slice)
	}
	it.index++
	return it.slice[it.index-1], nil
}

func (it *Parser) isAndSkip(expected string) bool {
	if it.index < len(it.slice) && it.slice[it.index] == expected {
		it.index++
		return true
	} else {
		return false
	}
}

func (it *Parser) isEnd() bool {
	return it.index == len(it.slice)
}

func (it *Parser) skip(expected ...string) error {
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

type varTypePairBracket struct {
	pairs []varTypePair
}

type varTypePair struct {
	Var  string
	Type string
}

type SingletonVar string

type FnReturnVar struct {
	FcFnRetVal
}

type FcFnRetVal struct {
	fn         Fc
	typeParams []FcStr
	varParams  []Fc
}

type Declaration interface{}

// 变量和函数是一等公民。它们的表现形式是：1. 单纯的string 2. 函数返回值
type Fc interface{}

type FcStr string

type Var interface{}
