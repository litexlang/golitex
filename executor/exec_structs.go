package executor

type ExecStatus uint8

const (
	TRUE ExecStatus = iota
	UNKNOWN
)

type ExecValue struct {
	status  ExecStatus
	message string
}
