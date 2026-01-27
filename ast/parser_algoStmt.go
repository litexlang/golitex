// Copyright Jiachen Shen.
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

package litex_ast

import (
	// "fmt"
	glob "golitex/glob"
)

func (p *TbParser) algoStmt(tb *tokenBlock) (AlgoStmt, error) {
	if tb.header.is(glob.KeywordIf) {
		return p.algoIfStmt(tb)
	}

	if tb.header.is(glob.KeywordReturn) {
		return p.algoReturnStmt(tb)
	}

	return p.Stmt(tb)
	// panic("not implemented")
}

// func (p *TbParser) proveAlgoStmt(tb *tokenBlock) (ProveAlgoStmt, error) {
// 	if tb.header.is(glob.KeywordIf) {
// 		return p.proveAlgoIfStmt(tb)
// 	}
//
// 	if tb.header.is(glob.KeywordReturn) {
// 		return p.proveAlgoReturnStmt(tb)
// 	}
//
// 	// In prove_algo, only if and return statements are allowed at the top level
// 	// Other statements like facts should be part of return or if blocks
// 	return nil, fmt.Errorf("unexpected statement in prove_algo, only 'if' and 'return' are allowed")
// }

// func (p *TbParser) proveAlgoIfStmt(tb *tokenBlock) (*ProveAlgoIfStmt, error) {
// 	err := tb.header.skip(glob.KeywordIf)
// 	if err != nil {
// 		return nil, ErrInLine(err, tb)
// 	}
//
// 	condition, err := p.inlineFacts_checkUniDepth0(tb, []string{glob.KeySymbolColon})
// 	if err != nil {
// 		return nil, ErrInLine(err, tb)
// 	}
//
// 	thenFacts := []ProveAlgoStmt{}
// 	for _, bodyStmt := range tb.body {
// 		stmt, err := p.proveAlgoStmt(&bodyStmt)
// 		if err != nil {
// 			return nil, ErrInLine(err, tb)
// 		}
// 		thenFacts = append(thenFacts, stmt)
// 	}
//
// 	return NewProveAlgoIfStmt(condition, thenFacts, tb.line), nil
// }

func (p *TbParser) algoIfStmt(tb *tokenBlock) (*AlgoIfStmt, error) {
	err := tb.header.skip(glob.KeywordIf)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	condition, err := p.inlineFacts_checkUniDepth0(tb, []string{glob.KeySymbolColon})
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	thenFacts := []AlgoStmt{}
	for _, bodyStmt := range tb.body {
		stmt, err := p.algoStmt(&bodyStmt)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		thenFacts = append(thenFacts, stmt)
	}

	return NewAlgoIfStmt(condition, thenFacts, tb.line), nil
}

func (p *TbParser) algoReturnStmt(tb *tokenBlock) (*AlgoReturnStmt, error) {
	err := tb.header.skip(glob.KeywordReturn)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	obj, err := p.Obj(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	return NewAlgoReturnStmt(obj, tb.line), nil
}

// func (p *TbParser) proveAlgoReturnStmt(tb *tokenBlock) (*ProveAlgoReturnStmt, error) {
// 	err := tb.header.skip(glob.KeywordReturn)
// 	if err != nil {
// 		return nil, err
// 	}
//
// 	// 首先检查是否到达末尾 - 如果到达，说明没有相关的 fact or by
// 	if tb.header.ExceedEnd() {
// 		return NewProveAlgoReturnStmt([]FactOrByStmt{}, tb.line), nil
// 	}
//
// 	// 没到最后，检查是否是 colon
// 	curToken, err := tb.header.currentToken()
// 	if err != nil {
// 		return nil, err
// 	}
//
// 	if curToken == glob.KeySymbolColon {
// 		// 是 colon，跳过它然后取 body
// 		err = tb.header.skip(glob.KeySymbolColon)
// 		if err != nil {
// 			return nil, err
// 		}
//
// 		// return: with colon - parse body which may contain facts or by statements
// 		factOrBySlice := []FactOrByStmt{}
// 		for _, bodyBlock := range tb.body {
// 			// Check if it's a by statement
// 			if bodyBlock.header.is(glob.KeywordBy) {
// 				byStmt, err := p.byStmt(&bodyBlock)
// 				if err != nil {
// 					return nil, err
// 				}
// 				factOrBySlice = append(factOrBySlice, byStmt.(FactOrByStmt))
// 			} else {
// 				// Otherwise parse as fact
// 				fact, err := p.factStmt(&bodyBlock, UniFactDepth0)
// 				if err != nil {
// 					return nil, err
// 				}
// 				factOrBySlice = append(factOrBySlice, fact)
// 			}
// 		}
// 		return NewProveAlgoReturnStmt(factOrBySlice, tb.line), nil
// 	}
//
// 	// 不是 colon，说明是单行的结果
// 	// Check if it's a by statement
// 	if tb.header.is(glob.KeywordBy) {
// 		byStmt, err := p.byStmt(tb)
// 		if err != nil {
// 			return nil, err
// 		}
// 		return NewProveAlgoReturnStmt([]FactOrByStmt{byStmt.(FactOrByStmt)}, tb.line), nil
// 	}
//
// 	// Otherwise parse as fact
// 	fact, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, []string{})
// 	if err != nil {
// 		return nil, err
// 	}
// 	return NewProveAlgoReturnStmt([]FactOrByStmt{fact}, tb.line), nil
// }
