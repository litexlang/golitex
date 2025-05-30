// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_ast

// import (
// 	"fmt"
// 	glob "golitex/glob"
// )

// type SpecFactIndexInLogicExprAndItself struct {
// 	Stmt    *SpecFactStmt
// 	Indexes []uint8
// }

// func (stmt *LogicExprStmt) SpecFactIndexPairs(indexes []uint8) ([]SpecFactIndexInLogicExprAndItself, error) {
// 	pairs := []SpecFactIndexInLogicExprAndItself{}
// 	for i, fact := range stmt.Facts {
// 		if specFact, ok := fact.(*SpecFactStmt); ok {
// 			curIndexes := make([]uint8, len(indexes))
// 			copy(curIndexes, indexes)
// 			curIndexes = append(curIndexes, uint8(i))
// 			pairs = append(pairs, SpecFactIndexInLogicExprAndItself{specFact, curIndexes})
// 			continue
// 		}

// 		if logicExpr, ok := fact.(*LogicExprStmt); ok {
// 			curIndexes := make([]uint8, len(indexes))
// 			copy(curIndexes, indexes)
// 			currentPairs, err := logicExpr.SpecFactIndexPairs(curIndexes)
// 			if err != nil {
// 				return nil, err
// 			}
// 			pairs = append(pairs, currentPairs...)
// 			continue
// 		}
// 	}
// 	if len(pairs) > glob.MaxLogicExprStmtIndexesSize {
// 		return nil, fmt.Errorf("logic expr stmt size too large")
// 	}
// 	return pairs, nil
// }

// var SpecFactUnderNoLogicalExprSig []uint8 = nil
