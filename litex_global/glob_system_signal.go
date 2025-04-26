package litex_global

type SysSignal uint8

const (
	SysSignalParseError SysSignal = iota
	SysSignalRuntimeError
	SysSignalTrue
	SysSignalFalse
	SysSignalUnknown
)

func (s SysSignal) String() string {
	return []string{"Syntax Error", "Runtime Error", "True", "False", "Unknown"}[s]
}
