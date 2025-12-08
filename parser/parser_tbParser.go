// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_parser

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"slices"
)

type tbParser struct {
}

func (p *tbParser) Stmt(tb *tokenBlock) (ast.Stmt, error) {
	cur, err := tb.header.currentToken()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	var ret ast.Stmt
	switch cur {
	case glob.KeywordProp:
		ret, err = p.defPropStmt(tb)
	case glob.KeywordExistProp:
		ret, err = p.defExistPropStmt(tb, glob.KeywordExistProp)
	case glob.KeywordFn:
		ret, err = p.defFnStmt(tb, true)
	case glob.KeywordLet:
		if tb.header.strAtCurIndexPlus(1) == glob.KeywordFn {
			tb.header.skip(glob.KeywordLet)
			ret, err = p.defFnStmt(tb, true)
		} else {
			ret, err = p.defObjStmt(tb)
		}
	case glob.KeywordHave:
		if tb.header.strAtCurIndexPlus(1) == glob.KeywordSet {
			if tb.header.strAtCurIndexPlus(2) == glob.KeywordFn {
				ret, err = p.haveSetFnStmt(tb)
			} else {
				ret, err = p.haveSetStmt(tb)
			}
		} else if tb.header.strAtCurIndexPlus(1) == glob.KeywordFn {
			if tb.header.strAtCurIndexPlus(2) == glob.KeySymbolColon {
				ret, err = p.haveFnStmt(tb)
				// } else if tb.header.strAtCurIndexPlus(4) == glob.KeywordLift {
				// 	ret, err = tb.haveFnLiftStmt()
			} else {
				ret, err = p.haveFnEqualStmt(tb)
			}
		} else if slices.Contains(tb.header.slice, glob.KeywordSt) {
			ret, err = p.haveObjStStmt(tb)
		} else if tb.header.strAtCurIndexPlus(1) == glob.KeywordCart {
			// Check for "have objName cart(...) = ..." pattern
			ret, err = p.haveObjFromCartSetStmt(tb)
		} else if slices.Contains(tb.header.slice, glob.KeySymbolEqual) {
			ret, err = p.haveObjEqualStmt(tb)
		} else {
			ret, err = p.haveObjInNonEmptySetStmt(tb)
		}
	case glob.KeywordClaim:
		ret, err = p.claimStmt(tb)
	case glob.KeywordProve:
		ret, err = p.proveStmt(tb)
	case glob.KeywordKnow:
		{
			if tb.TokenAtHeaderIndexIs(1, glob.KeySymbolAt) {
				if tb.TokenAtHeaderIndexIs(2, glob.KeywordExist) {
					ret, err = p.knowExistPropStmt(tb)
				} else {
					ret, err = p.knowPropStmt(tb)
				}
			} else {
				ret, err = p.knowFactStmt(tb)
			}
		}
	case glob.KeywordProveInEachCase:
		ret, err = p.proveInEachCaseStmt(tb)
	case glob.KeywordProveCaseByCase:
		ret, err = p.proveCaseByCaseStmt(tb)
	case glob.KeywordProveByEnum:
		ret, err = p.proveByEnum(tb)
	case glob.KeySymbolAt:
		ret, err = p.namedUniFactStmt(tb)
	case glob.KeywordFnTemplate:
		ret, err = p.fnTemplateStmt(tb)
	case glob.KeywordClear:
		ret, err = p.clearStmt(tb)
	case glob.KeywordProveByInduction:
		ret, err = tb.proveByInductionStmt()
	// case glob.KeywordProveInRangeSet:
	// 	ret, err = tb.proveInRangeSetStmt()
	case glob.KeywordProveInRange:
		ret, err = p.proveInRangeStmt(tb)
	case glob.KeywordProveIsTransitiveProp:
		ret, err = p.proveIsTransitivePropStmt(tb)
	case glob.KeywordProveIsCommutativeProp:
		ret, err = p.proveCommutativePropStmt(tb)
	case glob.KeywordAlgo:
		ret, err = p.algoDefStmt(tb)
	case glob.KeywordEval:
		ret, err = p.evalStmt(tb)
	case glob.KeywordProveAlgo:
		ret, err = p.defProveAlgoStmt(tb)
	case glob.KeywordBy:
		ret, err = p.byStmt(tb)
	case glob.KeywordProveByContradiction:
		ret, err = p.proveByContradictionStmt(tb)
	case glob.KeywordPrint:
		ret, err = p.printStmt(tb)
	case glob.KeywordHelp:
		ret, err = p.helpStmt(tb)
	case glob.KeywordDoNothing:
		ret, err = p.doNothingStmt(tb)
	case glob.KeywordImport:
		ret, err = p.importDirStmt(tb)
	case glob.KeywordHaveCartWithDim:
		ret, err = p.haveCartWithDimStmt(tb)
	default:
		ret, err = p.factsStmt(tb)
	}

	if err != nil {
		return nil, err
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of block")
	}

	return ret, nil
}

func (p *tbParser) defPropStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) defExistPropStmt(tb *tokenBlock, keyword string) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) defFnStmt(tb *tokenBlock, b bool) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) defObjStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) haveSetFnStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) haveSetStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) haveFnStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) haveFnEqualStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) haveObjStStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) haveObjFromCartSetStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) haveObjEqualStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) haveObjInNonEmptySetStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) claimStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) proveStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) knowExistPropStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) knowPropStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) knowFactStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) proveInEachCaseStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) proveCaseByCaseStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) proveByEnum(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) namedUniFactStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) fnTemplateStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) clearStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) proveInRangeStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) proveIsTransitivePropStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) proveCommutativePropStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) algoDefStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) evalStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) defProveAlgoStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) byStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) proveByContradictionStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) printStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) helpStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) doNothingStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) importDirStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) haveCartWithDimStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) factsStmt(tb *tokenBlock) (ast.Stmt, error) {
	return nil, fmt.Errorf("not implemented")
}
