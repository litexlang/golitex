package litexverifier

import (
	parser "golitex/litex_parser"
)

func (verifier *Verifier) verifyFuncFact(stmt *parser.FuncFactStmt) error {
	// TODO : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

	return verifier.verifyFuncFactLiterally(stmt)
}

func (verifier *Verifier) verifyFuncFactLiterally(stmt *parser.FuncFactStmt) error {
	verifier.roundAddOne()
	defer verifier.roundMinusOne()

	for curEnv := verifier.env; curEnv != nil; curEnv = curEnv.Parent {
		// searchedNode, err := verifier.useFuncFactMemToVerifyFuncFactAtEnvNodeByNode(stmt)
		searchedNode, err := curEnv.ConcreteFuncFactMemory.Mem.Search(stmt)
		if err != nil {
			return err
		}
		if searchedNode != nil {
			verifier.success("%v is true, verified by %v", stmt, searchedNode.Key)
			return nil
		}
	}

	if !verifier.round1() {
		return nil
	}

	return verifier.firstRoundVerifySpecFactLiterally(stmt)
}

// func (exec *Verifier) useFuncFactMemToVerifyFuncFactAtEnvNodeByNode(key *parser.FuncFactStmt) (*ds.Node[*parser.FuncFactStmt], error) {
// 	curNode := exec.env.FuncFactMemory.Mem.Root
// 	err := error(nil)
// 	searched := false
// 	for curNode != nil {
// 		// * 这里需要遍历当前的curNode的所有的参数，把参数替换成和该参数相等的参数，然后看下是否有相关的事实
// 		// * 类似数据库把有特定pattern的事实先全部搜到，然后遍历一遍些事实看看哪些能匹配上

// 		curNode, err, searched = exec.env.FuncFactMemory.Mem.SearchOneLayer(curNode, key)
// 		if err != nil {
// 			return nil, err
// 		}

// 		if searched {
// 			return curNode, nil
// 		}
// 	}

// 	return nil, nil
// }
