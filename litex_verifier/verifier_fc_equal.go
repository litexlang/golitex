package litexverifier

import (
	"fmt"
	cmp "golitex/litex_comparator"
	env "golitex/litex_env"
	memory "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func (ver *Verifier) FcEqual(left, right parser.Fc, specMode bool) (bool, error) {
	ver.addRound()
	defer ver.minusRound()

	// check whether given left or right is uniParam
	concreteLeft := ver.asConFc(left)
	if concreteLeft != nil {
		left = concreteLeft
	}
	concreteRight := ver.asConFc(right)
	if concreteRight != nil {
		right = concreteRight
	}

	ok, err := ver.fcEqualSpec(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if specMode {
		return false, nil
	}

	if !ver.round1() {
		return false, nil
	}

	return false, nil
}

func (ver *Verifier) fcFnCallPipeEqual(left, right *parser.FcFnCallPipe, specMode bool) (bool, error) {
	// 如果两个函数的名字一样，每个参数都一样，那也行
	// ret, err := cmp.CmpFcLiterally(&left.FnHead, &right.FnHead)
	ret, err := ver.FactStmt(&parser.SpecFactStmt{IsTrue: true, Opt: parser.FcAtom{PkgName: "", OptName: "="}, Params: []parser.Fc{&left.FnHead, &right.FnHead}})
	if err != nil {
		return false, err
	}

	if !ret {
		return false, nil
	}

	if len(left.CallPipe) != len(right.CallPipe) {
		return false, nil
	}

	for i := 0; i < len(left.CallPipe); i++ {
		if len(left.CallPipe[i].Params) != len(right.CallPipe[i].Params) {
			return false, nil
		}

		for j := 0; j < len(left.CallPipe[i].Params); j++ {
			ok, err := ver.FcEqual(left.CallPipe[i].Params[j], right.CallPipe[i].Params[j], specMode)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		}

	}

	if ver.round1() {
		ver.successMsgEnd(fmt.Sprintf("%v = %v", left.String(), right.String()), "use known facts")
	} else {
		ver.successNoMsg()
	}

	return true, nil
}

func (ver *Verifier) FcEqualSpecInSpecMemAtEnv(curEnv *env.Env, left parser.Fc, right parser.Fc) (bool, error) {
	key := memory.EqualFactMemoryTreeNode{FcAsKey: left, Values: []*parser.Fc{}}

	searchedNode, err := curEnv.EqualFactMem.Mem.TreeSearch(&key)

	if err != nil {
		return false, err
	}

	if searchedNode == nil {
		return false, nil
	}

	for _, equalFc := range searchedNode.Key.Values {
		cmpRet, err := cmp.CmpFcLiterally(*equalFc, right) // 只能用直接比较法
		// ok, err := ver.fcEqualSpec(*equalFc, right) // 这会导致无限循环
		if err != nil {
			return false, err
		}
		if cmpRet == 0 {
			return true, nil
		}
	}

	return false, nil
}
