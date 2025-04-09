package litex_verifier

// verState的工作原理类似Unix file permission
// 每个verifier方法都需要传入state，一方面是注入specMode，一方面是判断是否要打印
type VerState uint8

const (
	SpecMsg VerState = iota
	SpecNoMsg
	// AnyMsg
	// AnyNoMsg
	Round0Msg
	Round0NoMsg
	Round1Msg
	Round1NoMsg
)

func (e VerState) requireMsg() bool {
	if e == SpecMsg || e == Round0Msg || e == Round1Msg {
		return true
	} else {
		return false
	}
}

func (e VerState) isSpec() bool {
	if e == SpecMsg || e == SpecNoMsg {
		return true
	} else {
		return false
	}
}

func (e VerState) addRound() VerState {
	switch e {
	case Round0Msg:
		return Round1Msg
	case Round0NoMsg:
		return Round1NoMsg
	case Round1Msg:
		return SpecMsg
	case Round1NoMsg:
		return SpecNoMsg
	default:
		return e
	}
}

// func (e VerState) noMsg() VerState {
// 	switch e {
// 	case Round0Msg:
// 		return Round0NoMsg
// 	case Round1Msg:
// 		return Round1NoMsg
// 	case SpecMsg:
// 		return SpecNoMsg
// 	}
// 	return e
// }
