package litexverifier

import "fmt"

func (ver *Verifier) successMsg(stmtStr, stmtVerifiedBy string) {
	if stmtStr != "" {
		*ver.Message = append(*ver.Message, stmtStr)
	}
	if stmtVerifiedBy != "" {
		message := fmt.Sprintf("is true. proved by\n%v", stmtVerifiedBy)
		*ver.Message = append(*ver.Message, message)
	}
}

func (ver *Verifier) unknownMsg(format string, args ...any) {
	message := fmt.Sprintf(format, args...)
	*ver.Message = append(*ver.Message, message)
}
