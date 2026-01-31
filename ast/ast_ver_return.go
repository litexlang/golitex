package litex_ast

type VerRet interface {
	verRet()
	IsTrue() bool
	IsUnknown() bool
	IsErr() bool
	IsNotTrue() bool
}

type TrueVerRet struct {
	ToCheck                FactStmt
	VerifiedByKnownFact    FactStmt
	VerifiedByBuiltinRules string
}

func (r *TrueVerRet) verRet()         {}
func (r *TrueVerRet) IsTrue() bool    { return true }
func (r *TrueVerRet) IsUnknown() bool { return false }
func (r *TrueVerRet) IsErr() bool     { return false }
func (r *TrueVerRet) IsNotTrue() bool { return false }

type UnknownVerRet struct {
	ToCheck FactStmt
}

func (r *UnknownVerRet) verRet()         {}
func (r *UnknownVerRet) IsTrue() bool    { return false }
func (r *UnknownVerRet) IsUnknown() bool { return true }
func (r *UnknownVerRet) IsErr() bool     { return false }
func (r *UnknownVerRet) IsNotTrue() bool { return true }

type ErrVerRet struct {
	ToCheck FactStmt
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
