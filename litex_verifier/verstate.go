package litex_verifier

// verState的工作原理类似Unix file permission
// 每个verifier方法都需要传入state，一方面是注入specMode，一方面是判断是否要打印
type VerState uint8

const (
	SpecMsg VerState = iota
	SpecNoMsg
	AnyMsg
	AnyNoMsg
)

func (e VerState) requireMsg() bool {
	if e == SpecMsg || e == AnyMsg {
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

func (e VerState) spec() VerState {
	if e == AnyMsg {
		return SpecMsg
	} else if e == AnyNoMsg {
		return SpecNoMsg
	}
	return e
}

func (e VerState) noMsg() VerState {
	if e == SpecMsg {
		return SpecNoMsg
	} else if e == AnyMsg {
		return AnyNoMsg
	}
	return e
}
