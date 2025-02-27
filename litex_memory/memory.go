package litexmemory

import (
	"fmt"
	parser "golitex/litex_parser"
	"strings"
)

const fcFnCallChainMemKeyLinker = "~"
const calledFcFnRetValueKeyMemKeySpecifier = "@"

func getMemoryKey(fc parser.Fc) (string, error) {
	if value, ok := fc.(*parser.FcFnRetValue); ok {
		ret, err := getMemoryKey(value.Fn)
		if err != nil {
			return "", err
		}

		return calledFcFnRetValueKeyMemKeySpecifier + ret, nil
	} else if value, ok := fc.(parser.FcStr); ok {
		return string(value), nil
	} else if value, ok := fc.(*parser.FcMemChain); ok {
		fcs := []string{}
		for _, fc := range *(value) {
			key, err := getMemoryKey(fc)
			if err != nil {
				return "", err
			}
			fcs = append(fcs, key)
		}
		return strings.Join(fcs, fcFnCallChainMemKeyLinker), nil
	}

	return "", &MemoryErr{fmt.Errorf("invalid Fc type")}
}
