package litexmemory

import (
	"fmt"
	parser "golitex/litex_parser"
)

func (mem *RedBlackTree[T]) SearchInEnv(env *Env, key T) (*Node[T], error) {
	// TODO: even when given key is different as tree key, we might still view them as the same. For example, when we know x = y, and we have $p(x), we now are verifying $p(y). As tree node, $p(x) is different from $p(y), but since x = y they are the same. So $p(y) should also be verified.

	return mem.Search(key)
}

func (mem *RedBlackTree[T]) SearchInEnvLayerByLayer(env *Env, key T) (*Node[T], error) {
	curNode := mem.Root
	var err error = nil
	searched := false
	for curNode != nil {
		curNode, err, searched = mem.SearchOneLayer(curNode, key)
		if err != nil {
			return nil, err
		}

		if searched {
			return curNode, nil
		}
	}

	return nil, nil
}

type FcChainParamEql *[]FcRetValParamEql

type FcRetValParamEql struct {
	typeParamEql [][]parser.Fc
	varParamEql  [][]parser.Fc
}

// func (env *Env) searchEquivalentFuncFactParamsInAllEnvs(key *parser.FuncFactStmt) (searchEquivalentFuncFactReturn, error) {
// 	switch key.Fc.(type) {
// 	case parser.FcStr:
// 		return nil, fmt.Errorf("Invalid FuncFact %v", key.Fc)
// 	case *parser.FcFnRetValue:
// 		return searchEquivalentFcFnRetFuncFactParamsInAllEnvs(key.Fc.(*parser.FcFnRetValue))
// 	case *parser.FcChain:
// 		return searchEquivalentFcChainFuncFactParamsInAllEnvs(key.Fc.(*parser.FcChain))
// 	}
// 	panic("")
// }

func searchEquivalentFcFnRetFuncFactParamsInAllEnvs(key *parser.FcFnRetValue) (FcRetValParamEql, error) {
	return FcRetValParamEql{}, fmt.Errorf("Invalid FuncFact %v", key)
}

func searchEquivalentFcChainFuncFactParamsInAllEnvs(key *parser.FcChain) (FcRetValParamEql, error) {
	return FcRetValParamEql{}, fmt.Errorf("Invalid FuncFact %v", key)
}
