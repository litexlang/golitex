package litex_env

import (
	ast "golitex/ast"
	glob "golitex/glob"
	"strconv"
)

func (ie *InferenceEngine) newTrueEqual(fact *ast.SpecFactStmt) glob.GlobRet {
	ret := ie.equalFactByCart(fact)
	if ret.IsErr() {
		return ret
	}

	// 处理 tuple 相等的情况
	ret = ie.equalFactByTupleEquality(fact.Params[0], fact.Params[1])
	if ret.IsErr() {
		return ret
	}

	// 处理 x = {1, 2, 3} 的情况
	ret = ie.equalFactByListSetEquality(fact.Params[0], fact.Params[1])
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}

// equalFactByCart handles postprocessing for x = cart(x1, x2, ..., xn)
// It generates:
//   - is_cart(x) fact
//   - dim(x) = len(cart.Params) fact
//   - proj(x, i+1) = cart.Params[i] facts for each i
func (ie *InferenceEngine) equalFactByCart(fact *ast.SpecFactStmt) glob.GlobRet {
	cart, ok := fact.Params[1].(*ast.FnObj)
	if !ok || !ast.IsAtomObjAndEqualToStr(cart.FnHead, glob.KeywordCart) {
		return glob.NewEmptyGlobUnknown()
	}

	// 让 $is_cart(x) 成立
	isCartFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsCart), []ast.Obj{fact.Params[0]}, glob.BuiltinLine)
	ret := ie.Env.NewFact(isCartFact)
	if ret.IsErr() {
		return ret
	}

	// dim(x) = len(cart.Params)
	dimFn := ast.NewFnObj(ast.Atom(glob.KeywordSetDim), []ast.Obj{fact.Params[0]})
	dimValue := ast.Atom(strconv.Itoa(len(cart.Params)))
	dimEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{dimFn, dimValue}, glob.BuiltinLine)
	ret = ie.Env.NewFact(dimEqualFact)
	if ret.IsErr() {
		return ret
	}

	// proj(x, i+1) = cart.Params[i] for each i
	for i, cartParam := range cart.Params {
		projFn := ast.NewFnObj(ast.Atom(glob.KeywordProj), []ast.Obj{fact.Params[0], ast.Atom(strconv.Itoa(i + 1))})
		projEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{projFn, cartParam}, glob.BuiltinLine)
		ret = ie.Env.NewFact(projEqualFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.NewGlobTrue("")
}
