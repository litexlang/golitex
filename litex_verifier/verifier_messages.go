package litexverifier

import "fmt"

func (ver *Verifier) successMsg(stmtStr, stmtVerifiedBy string) {
	if stmtStr != "" {
		*ver.Messages = append(*ver.Messages, stmtStr)
	}
	if stmtVerifiedBy != "" {
		message := fmt.Sprintf("is true. proved by\n%v", stmtVerifiedBy)
		*ver.Messages = append(*ver.Messages, message)
	}
}

func (ver *Verifier) unknownMsg(format string, args ...any) {
	message := fmt.Sprintf(format, args...)
	*ver.Messages = append(*ver.Messages, message)
}

func (ver *Verifier) newMsg(format string, args ...any) {
	message := fmt.Sprintf(format, args...)
	*ver.Messages = append(*ver.Messages, message)
}
