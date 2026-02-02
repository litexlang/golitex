package litex_global

type StmtRet interface {
	stmtRet()
	String() string
}

type TrueStmtRet struct {
	Msg string
}

type UnknownStmtRet struct {
	Msg string
}

type ErrStmtRet struct {
	Msg string
}

func (r *TrueStmtRet) stmtRet()    {}
func (r *UnknownStmtRet) stmtRet() {}
func (r *ErrStmtRet) stmtRet()     {}

func (r *TrueStmtRet) String() string {
	return r.Msg
}

func (r *UnknownStmtRet) String() string {
	return r.Msg
}

func (r *ErrStmtRet) String() string {
	return r.Msg
}
