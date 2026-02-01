package litex_ast

type VerRet interface {
	verRet()
	IsTrue() bool
	IsUnknown() bool
	IsErr() bool
	IsNotTrue() bool
	ToStmtRet() StmtRet
	AddExtraInfo(extraInfo string) VerRet
	AddExtraInfos(extraInfos []string) VerRet
	GetExtraInfos() []string
	GetToCheck() FactStmt
}

type TrueVerRet struct {
	ToCheck                FactStmt
	VerifiedByKnownFact    FactStmt
	VerifiedByBuiltinRules string
	ExtraInfo              []string
}

func (r *TrueVerRet) verRet()         {}
func (r *TrueVerRet) IsTrue() bool    { return true }
func (r *TrueVerRet) IsUnknown() bool { return false }
func (r *TrueVerRet) IsErr() bool     { return false }
func (r *TrueVerRet) IsNotTrue() bool { return false }

type UnknownVerRet struct {
	ToCheck   FactStmt
	ExtraInfo []string
}

func (r *UnknownVerRet) verRet()         {}
func (r *UnknownVerRet) IsTrue() bool    { return false }
func (r *UnknownVerRet) IsUnknown() bool { return true }
func (r *UnknownVerRet) IsErr() bool     { return false }
func (r *UnknownVerRet) IsNotTrue() bool { return true }

type ErrVerRet struct {
	ToCheck   FactStmt
	ExtraInfo []string
}

func (r *ErrVerRet) verRet()         {}
func (r *ErrVerRet) IsTrue() bool    { return false }
func (r *ErrVerRet) IsUnknown() bool { return false }
func (r *ErrVerRet) IsErr() bool     { return true }
func (r *ErrVerRet) IsNotTrue() bool { return true }

func NewTrueVerRet(ToCheck FactStmt, VerifiedByKnownFact FactStmt, VerifiedByBuiltinRules string) *TrueVerRet {
	return &TrueVerRet{ToCheck: ToCheck, VerifiedByKnownFact: VerifiedByKnownFact, VerifiedByBuiltinRules: VerifiedByBuiltinRules}
}

func NewUnknownVerRet(ToCheck FactStmt) *UnknownVerRet {
	return &UnknownVerRet{ToCheck: ToCheck}
}

func NewErrVerRet(ToCheck FactStmt) *ErrVerRet {
	return &ErrVerRet{ToCheck: ToCheck}
}

func NewEmptyVerRetErr() *ErrVerRet {
	return &ErrVerRet{ToCheck: nil}
}

func NewEmptyUnknownVerRet() *UnknownVerRet {
	return &UnknownVerRet{ToCheck: nil}
}

func (r *TrueVerRet) ToStmtRet() StmtRet {
	return NewTrueStmtEmptyRet(r.ToCheck).AddVerifyProcess(r)
}
func (r *UnknownVerRet) ToStmtRet() StmtRet {
	return NewUnknownStmtEmptyRet(r.ToCheck)
}
func (r *ErrVerRet) ToStmtRet() StmtRet {
	return NewErrStmtEmptyRet(r.ToCheck)
}

func (r *UnknownVerRet) AddExtraInfo(extraInfo string) VerRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfo)
	return r
}
func (r *ErrVerRet) AddExtraInfo(extraInfo string) VerRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfo)
	return r
}
func (r *ErrVerRet) AddErr(err error) *ErrVerRet {
	r.ExtraInfo = append(r.ExtraInfo, err.Error())
	return r
}

func (r *TrueVerRet) AddExtraInfos(extraInfos []string) VerRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfos...)
	return r
}

func (r *TrueVerRet) GetExtraInfos() []string {
	return r.ExtraInfo
}

func (r *UnknownVerRet) AddExtraInfos(extraInfos []string) VerRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfos...)
	return r
}
func (r *UnknownVerRet) GetExtraInfos() []string {
	return r.ExtraInfo
}
func (r *ErrVerRet) AddExtraInfos(extraInfos []string) VerRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfos...)
	return r
}
func (r *ErrVerRet) GetExtraInfos() []string {
	return r.ExtraInfo
}

func (r *TrueVerRet) AddExtraInfo(extraInfo string) VerRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfo)
	return r
}

func (r *TrueVerRet) GetToCheck() FactStmt {
	return r.ToCheck
}
func (r *UnknownVerRet) GetToCheck() FactStmt {
	return r.ToCheck
}
func (r *ErrVerRet) GetToCheck() FactStmt {
	return r.ToCheck
}
