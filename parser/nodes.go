package parser

import "fmt"

type StrIterator struct {
	index int
	slice []string
}

func (i *StrIterator) next() (string, error) {
	if i.index >= len(i.slice) {
		return "", fmt.Errorf("unexpected end of slice %v", i.slice)
	}
	i.index++
	return i.slice[i.index-1], nil
}

func (i *StrIterator) skip(expected ...string) error {
	if i.index >= len(i.slice) {
		return fmt.Errorf("unexpected end of slice %v", i.slice)
	}

	if len(expected) == 0 {
		i.index++
		return nil
	}

	if i.slice[i.index] == expected[0] {
		i.index++
	} else {
		return fmt.Errorf("expected '%s', but got '%s'", expected[0], i.slice[i.index])
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
