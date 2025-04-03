package litexverifier

import (
	parser "golitex/litex_parser"
)

func (ver *Verifier) CondFact(stmt *parser.CondFactStmt, state VerState) (bool, error) {
	// 	ok, err := ver.CondFactSpec(stmt, state)
	// 	if err != nil {
	// 		return false, err
	// 	}
	// 	if ok {
	// 		return true, nil
	// 	}

	// 	if !ver.round1() {
	// 		return false, nil
	// 	}

	// 	// TODO

	// 	return ver.CondFactCond(stmt, state)

	// 	// TODO: CondFactUni
	// }

	// func (ver *Verifier) CondFactSpec(stmt *parser.CondFactStmt, state VerState) (bool, error) {
	ver.newEnv(nil)
	defer ver.deleteEnvAndRetainMsg() // 万一cond里有condFact，那要保证能回到原来的环境

	for _, condFact := range stmt.CondFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	for _, thenFact := range stmt.ThenFacts {
		ok, err := ver.FactStmt(&thenFact, state) // 貌似这里不用把state换成spec，比如用户输入condFact，然后下面的事实都正常运行，只不过需要现知道一下condFacts
		if err != nil {
			return false, err
		}
		if !ok {
			// 			if ver.round1() {
			// 	ver.unknownWithMsg("%v is unknown: %v is unknown", stmt, thenFact)
			// 	return false, nil
			// }
			// if state.isSpec()() {
			// 	ver.unknownWithMsg("%v is unknown: %v is unknown", stmt, thenFact)
			// 	return false, nil
			// } else {
			// ver.unknownNoMsg()
			return false, nil
			// }
		}
	}

	// if ver.round1() {
	// 	ver.successWithMsg("%v is true", stmt.String())
	// 	return true, nil
	// } else {
	// 	ver.successNoMsg()
	// 	return true, nil
	// }

	if state.requireMsg() {
		ver.successMsgEnd(stmt.String(), "")
		// ver.env.Parent.NewMsg(fmt.Sprintf("%v\nis true", stmt.String()))
		return true, nil
	} else {
		ver.successNoMsg()
		return true, nil
	}
}
