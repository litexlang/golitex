package litex_ast

type StmtRet interface {
	stmtRet()
	IsTrue() bool
	IsUnknown() bool
	IsErr() bool
	IsNotTrue() bool
}

type TrueStmtRet struct {
	Stmt              Stmt
	Define            []string
	NewFact           []Stmt
	VerifyProcess     []VerRet
	Infer             []Stmt
	InnerStmtRetSlice []StmtRet
	ExtraInfo         []string
}

func (r *TrueStmtRet) stmtRet()        {}
func (r *TrueStmtRet) IsTrue() bool    { return true }
func (r *TrueStmtRet) IsUnknown() bool { return false }
func (r *TrueStmtRet) IsErr() bool     { return false }
func (r *TrueStmtRet) IsNotTrue() bool { return false }
func (r *TrueStmtRet) AddDefine(define string) *TrueStmtRet {
	r.Define = append(r.Define, define)
	return r
}
func (r *TrueStmtRet) AddNewFact(newFact Stmt) *TrueStmtRet {
	r.NewFact = append(r.NewFact, newFact)
	return r
}
func (r *TrueStmtRet) AddVerifyProcess(verifyProcess VerRet) *TrueStmtRet {
	r.VerifyProcess = append(r.VerifyProcess, verifyProcess)
	return r
}
func (r *TrueStmtRet) AddInfer(infer Stmt) *TrueStmtRet {
	r.Infer = append(r.Infer, infer)
	return r
}
func (r *TrueStmtRet) AddInnerStmtRet(innerStmtRet StmtRet) *TrueStmtRet {
	r.InnerStmtRetSlice = append(r.InnerStmtRetSlice, innerStmtRet)
	return r
}
func (r *TrueStmtRet) AddExtraInfo(extraInfo string) *TrueStmtRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfo)
	return r
}

type UnknownStmtRet struct {
	Stmt      Stmt
	ExtraInfo []string
}

func (r *UnknownStmtRet) stmtRet()        {}
func (r *UnknownStmtRet) IsTrue() bool    { return false }
func (r *UnknownStmtRet) IsUnknown() bool { return true }
func (r *UnknownStmtRet) IsErr() bool     { return false }
func (r *UnknownStmtRet) IsNotTrue() bool { return true }

type ErrStmtRet struct {
	Stmt      Stmt
	ExtraInfo []string
}

func (r *ErrStmtRet) stmtRet()        {}
func (r *ErrStmtRet) IsTrue() bool    { return false }
func (r *ErrStmtRet) IsUnknown() bool { return false }
func (r *ErrStmtRet) IsErr() bool     { return true }
func (r *ErrStmtRet) IsNotTrue() bool { return true }

func NewTrueStmtEmptyRet(stmt Stmt) *TrueStmtRet {
	return &TrueStmtRet{Stmt: stmt, Define: []string{}, NewFact: []Stmt{}, VerifyProcess: []VerRet{}, Infer: []Stmt{}, InnerStmtRetSlice: []StmtRet{}, ExtraInfo: []string{}}
}
func NewUnknownStmtEmptyRet(stmt Stmt) *UnknownStmtRet {
	return &UnknownStmtRet{Stmt: stmt, ExtraInfo: []string{}}
}
func NewErrStmtEmptyRet(stmt Stmt) *ErrStmtRet {
	return &ErrStmtRet{Stmt: stmt, ExtraInfo: []string{}}
}
