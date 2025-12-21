package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ie *InferenceEngine) newUserDefinedTruePureFactByDef(fact *ast.SpecFactStmt) glob.GlobRet {
	// 通过 prop 定义中的 iff 和 implication 规则，推导出后续结论
	// 因为 prop 的定义包含了 iff（当且仅当）和 implication（蕴含）关系，
	// 所以当该 prop 为真时，可以推导出定义中指定的后续事实
	propDef := ie.EnvMgr.GetPropDef(fact.PropName)
	if propDef == nil {
		// TODO 这里需要考虑prop的定义是否在当前包中。当然这里有点复杂，因为如果是内置的prop，那么可能需要到builtin包中去找
		return glob.NewGlobTrue("")
	}

	iffFacts := []string{}
	implicationFacts := []string{}

	uniMap := map[string]ast.Obj{}
	for i, propParam := range propDef.DefHeader.Params {
		uniMap[propParam] = fact.Params[i]
	}

	// 通过 iff（当且仅当）规则推导出的事实
	for _, thenFact := range propDef.IffFactsOrNil {
		instantiated, err := thenFact.InstantiateFact(uniMap)
		if err != nil {
			return glob.ErrRet(err)
		}

		ret := ie.EnvMgr.newFactNoInfer(instantiated)

		// Note: Messages are now added to ExecRet in the caller, not to env.Msgs

		if ret.IsErr() {
			return ret
		}

		// Collect the instantiated fact itself as a derived fact
		if ret.IsTrue() {
			if specFact, ok := instantiated.(*ast.SpecFactStmt); ok {
				iffFacts = append(iffFacts, specFact.String())
			} else {
				iffFacts = append(iffFacts, instantiated.String())
			}
		}
	}

	// 通过 implication（蕴含）规则推导出的事实
	for _, thenFact := range propDef.ImplicationFactsOrNil {
		instantiated, err := thenFact.InstantiateFact(uniMap)
		if err != nil {
			return glob.ErrRet(err)
		}

		ret := ie.EnvMgr.newFactNoInfer(instantiated)

		// Note: Messages are now added to ExecRet in the caller, not to env.Msgs

		if ret.IsErr() {
			return ret
		}

		// Collect the instantiated fact itself as a derived fact
		if ret.IsTrue() {
			implicationFacts = append(implicationFacts, instantiated.String())
		}
	}

	// 构建返回消息，明确标注哪些来自 iff，哪些来自 implication
	derivedFacts := []string{}
	if len(iffFacts) > 0 || len(implicationFacts) > 0 {
		derivedFacts = append(derivedFacts, fmt.Sprintf("derive facts from %s:", fact.String()))
		derivedFacts = append(derivedFacts, iffFacts...)
		derivedFacts = append(derivedFacts, implicationFacts...)
		derivedFacts = append(derivedFacts, "")
	}

	return glob.NewGlobTrueWithMsgs(derivedFacts)
}
