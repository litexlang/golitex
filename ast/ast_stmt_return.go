package litex_ast

type StmtRet interface {
	stmtRet()
	IsTrue() bool
	IsUnknown() bool
	IsErr() bool
	IsNotTrue() bool
	AddExtraInfo(extraInfo string) StmtRet
	AddExtraInfos(extraInfos []string) StmtRet
	GetExtraInfos() []string
	AddVerifyProcesses(verifyProcesses []VerRet) StmtRet
	AddInfers(infers []InferRet) StmtRet
}

func (r *UnknownStmtRet) notTrueStmtRet() {}
func (r *ErrStmtRet) notTrueStmtRet()     {}
func (r *UnknownStmtRet) GetExtraInfos() []string {
	return r.ExtraInfo
}
func (r *ErrStmtRet) GetExtraInfos() []string {
	return r.ExtraInfo
}

type TrueStmtRet struct {
	Stmt              Stmt
	Define            []string
	VerifyProcess     []VerRet
	Infer             []InferRet
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
func (r *TrueStmtRet) AddVerifyProcess(verifyProcess VerRet) *TrueStmtRet {
	r.VerifyProcess = append(r.VerifyProcess, verifyProcess)
	return r
}
func (r *TrueStmtRet) AddInfer(infer InferRet) *TrueStmtRet {
	r.Infer = append(r.Infer, infer)
	return r
}
func (r *TrueStmtRet) AddInnerStmtRet(innerStmtRet StmtRet) *TrueStmtRet {
	r.InnerStmtRetSlice = append(r.InnerStmtRetSlice, innerStmtRet)
	return r
}

func (r *TrueStmtRet) AddInnerStmtRets(innerStmtRets []StmtRet) *TrueStmtRet {
	r.InnerStmtRetSlice = append(r.InnerStmtRetSlice, innerStmtRets...)
	return r
}

func (r *TrueStmtRet) AddDefines(defines []string) *TrueStmtRet {
	r.Define = append(r.Define, defines...)
	return r
}

type UnknownStmtRet struct {
	Stmt              Stmt
	Define            []string
	VerifyProcess     []VerRet
	Infer             []InferRet
	InnerStmtRetSlice []StmtRet
	ExtraInfo         []string
}

func (r *UnknownStmtRet) stmtRet()        {}
func (r *UnknownStmtRet) IsTrue() bool    { return false }
func (r *UnknownStmtRet) IsUnknown() bool { return true }
func (r *UnknownStmtRet) IsErr() bool     { return false }
func (r *UnknownStmtRet) IsNotTrue() bool { return true }

type ErrStmtRet struct {
	Stmt              Stmt
	Define            []string
	VerifyProcess     []VerRet
	Infer             []InferRet
	InnerStmtRetSlice []StmtRet
	ExtraInfo         []string
}

func (r *ErrStmtRet) stmtRet()        {}
func (r *ErrStmtRet) IsTrue() bool    { return false }
func (r *ErrStmtRet) IsUnknown() bool { return false }
func (r *ErrStmtRet) IsErr() bool     { return true }
func (r *ErrStmtRet) IsNotTrue() bool { return true }

func NewTrueStmtEmptyRet(stmt Stmt) *TrueStmtRet {
	return &TrueStmtRet{Stmt: stmt, Define: []string{}, VerifyProcess: []VerRet{}, Infer: []InferRet{}, InnerStmtRetSlice: []StmtRet{}, ExtraInfo: []string{}}
}
func NewUnknownStmtEmptyRet(stmt Stmt) *UnknownStmtRet {
	return &UnknownStmtRet{Stmt: stmt, ExtraInfo: []string{}}
}
func NewErrStmtEmptyRet(stmt Stmt) *ErrStmtRet {
	return &ErrStmtRet{Stmt: stmt, ExtraInfo: []string{}}
}

func (r *UnknownStmtRet) AddExtraInfo(extraInfo string) StmtRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfo)
	return r
}
func (r *ErrStmtRet) AddExtraInfo(extraInfo string) StmtRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfo)
	return r
}
func (r *TrueStmtRet) AddExtraInfo(extraInfo string) StmtRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfo)
	return r
}

func (r *UnknownStmtRet) AddExtraInfos(extraInfos []string) StmtRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfos...)
	return r
}
func (r *ErrStmtRet) AddExtraInfos(extraInfos []string) StmtRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfos...)
	return r
}
func (r *TrueStmtRet) AddExtraInfos(extraInfos []string) StmtRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfos...)
	return r
}

func (r *TrueStmtRet) GetExtraInfos() []string {
	return r.ExtraInfo
}

func (r *UnknownStmtRet) AddVerifyProcess(verifyProcess VerRet) StmtRet {
	r.VerifyProcess = append(r.VerifyProcess, verifyProcess)
	return r
}

func (r *ErrStmtRet) AddVerifyProcess(verifyProcess VerRet) StmtRet {
	r.VerifyProcess = append(r.VerifyProcess, verifyProcess)
	return r
}

func (r *UnknownStmtRet) AddInfer(infer InferRet) StmtRet {
	r.Infer = append(r.Infer, infer)
	return r
}

func (r *ErrStmtRet) AddInfer(infer InferRet) StmtRet {
	r.Infer = append(r.Infer, infer)
	return r
}

func StmtErrRet(stmt Stmt, err string) StmtRet {
	return NewErrStmtEmptyRet(stmt).AddExtraInfo(err)
}

func (r *UnknownStmtRet) AddVerifyProcesses(verifyProcesses []VerRet) StmtRet {
	r.VerifyProcess = append(r.VerifyProcess, verifyProcesses...)
	return r
}
func (r *ErrStmtRet) AddVerifyProcesses(verifyProcesses []VerRet) StmtRet {
	r.VerifyProcess = append(r.VerifyProcess, verifyProcesses...)
	return r
}
func (r *TrueStmtRet) AddVerifyProcesses(verifyProcesses []VerRet) StmtRet {
	r.VerifyProcess = append(r.VerifyProcess, verifyProcesses...)
	return r
}

func (r *UnknownStmtRet) AddInfers(infers []InferRet) StmtRet {
	r.Infer = append(r.Infer, infers...)
	return r
}
func (r *ErrStmtRet) AddInfers(infers []InferRet) StmtRet {
	r.Infer = append(r.Infer, infers...)
	return r
}
func (r *TrueStmtRet) AddInfers(infers []InferRet) StmtRet {
	r.Infer = append(r.Infer, infers...)
	return r
}
