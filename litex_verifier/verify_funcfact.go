package litexverifier

import (
	env "golitex/litex_env"
	mem "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func (ver *Verifier) SpecFact(stmt *parser.SpecFactStmt) (bool, error) {
	// TODO 判断一下传入进来的stmt是不是prop prop，就像数学归纳法这种。prop prop的特点是，它是prop，参数列表里也有prop。如果是的话，那就用其他方式来验证
	if isPropProp, err := ver.IsPropProp(stmt); err != nil {
		return false, err
	} else if isPropProp {
		return ver.PropPropFact(stmt)
	}

	if ok, err := ver.SpecFactSpec(stmt); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if !ver.round1() {
		return false, nil
	}

	if ok, err := ver.SpecFactCond(stmt); err != nil {
		return false, nil
	} else if ok {
		return true, nil
	}

	if ok, err := ver.SpecFactUni(stmt); err != nil {
		return false, nil
	} else if ok {
		return true, nil
	}

	ver.unknownNoMsg()
	return false, nil
}

func (ver *Verifier) SpecFactSpec(stmt *parser.SpecFactStmt) (bool, error) {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		if stmt.IsEqualFact() {
			return ver.EqualFactSpecAtEnv(curEnv, stmt)
		}

		searchedNode, got := curEnv.SpecFactMem.GetNode(stmt)
		if !got {
			continue
		}

		for _, knownFact := range searchedNode.Facts {
			if stmt.IsTrue != knownFact.IsTrue {
				continue
			}

			ok, err := ver.FcSliceEqual(&knownFact.Params, &stmt.Params, false)

			if err != nil {
				return false, err
			}

			if ok {
				if ver.round1() {
					ver.successWithMsg("", knownFact.String(stmt.Opt))
				} else {
					ver.successNoMsg()
				}
				return true, nil
			}
		}
	}
	return false, nil
}

func (ver *Verifier) SpecFactCond(stmt *parser.SpecFactStmt) (bool, error) {
	// Use cond fact to verify
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		ok, err := ver.SpecFactCondAtEnv(curEnv, stmt)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) SpecFactCondAtEnv(curEnv *env.Env, stmt *parser.SpecFactStmt) (bool, error) {
	searched, got := curEnv.CondFactMem.GetSpecFactNode(stmt)
	if !got {
		return false, nil
	}

LoopOverFacts:
	for _, knownFact := range searched.Facts {
		for _, f := range knownFact.Fact.CondFacts {
			ok, err := ver.FactStmt(f)
			if err != nil {
				return false, err
			}
			if !ok {
				continue LoopOverFacts
			}
		}

		verified, err := ver.FcSliceEqual(knownFact.Params, &stmt.Params, false)

		if err != nil {
			return false, err
		}

		if verified {
			if ver.round1() {
				ver.successWithMsg("", knownFact.Fact.String())
			} else {
				ver.successNoMsg()
			}
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) SpecFactUni(stmt *parser.SpecFactStmt) (bool, error) {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		ok, err := ver.SpecFactUniAtEnv(curEnv, stmt)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) SpecFactUniAtEnv(curEnv *env.Env, stmt *parser.SpecFactStmt) (bool, error) {
	searched, got := curEnv.UniFactMem.GetSpecFactNode(stmt)
	if !got {
		return false, nil
	}

	uniConMap := &map[string]parser.Fc{}
	for _, knownFact := range searched.Facts {
		// TODO： 这里要确保搜到的事实的每一位freeObj和concreteObj能对上，然后要记录一下每一位freeObj是哪个concreteObj。还要保证涉及到的Known UniFact的param都被match上了
		paramArrMap, ok, err := ver.matchStoredUniConSpecFacts(knownFact, stmt)
		if err != nil {
			return false, err
		}
		if !ok {
			continue
		}

		uniConMap, ok, err = ver.ValuesUnderKeyInMatchMapEqualSpec(paramArrMap)
		if err != nil {
			return false, err
		}
		if !ok {
			continue
		}

		ok, err = ver.specFactUniWithUniConMap(&knownFact, stmt, uniConMap)
		if err != nil {
			return false, err
		}
		if ok {
			ver.successWithMsg("", knownFact.String())
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) ValuesUnderKeyInMatchMapEqualSpec(paramArrMap *map[string][]parser.Fc) (*map[string]parser.Fc, bool, error) {
	newMap := map[string]parser.Fc{}
LoopParamArrMap:
	for key, value := range *paramArrMap {
		if len(value) == 1 {
			continue
		}

		for i := 1; i < len(value); i++ {
			ok, err := ver.fcEqualSpec(value[0], value[i])
			if err != nil {
				return nil, false, err
			}
			if !ok {
				continue LoopParamArrMap
			}
		}

		newMap[key] = value[0]
	}

	return &newMap, true, nil
}

func (ver *Verifier) specFactUniWithUniConMap(knownStmt *mem.StoredUniSpecFact, stmt *parser.SpecFactStmt, uniConMap *map[string]parser.Fc) (bool, error) {
	return false, nil
}
