package litexexecutor

type ExecStatus uint8

const (
	ExecTrue ExecStatus = iota
	ExecUnknown
	ExecError
)

type ExecValue struct {
	status  ExecStatus
	message string
}
