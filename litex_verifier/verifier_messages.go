package litexverifier

import "fmt"

func (ver *Verifier) successMsg(stmtStr, stmtVerifiedBy string) {
	if stmtStr != "" {
		*ver.Message = append(*ver.Message, stmtStr)
	}
	message := fmt.Sprintf("is true. proved by\n%v", stmtVerifiedBy)
	*ver.Message = append(*ver.Message, message) // 新消息插在后面
}

func (ver *Verifier) unknownMsg(format string, args ...any) {
	message := fmt.Sprintf(format, args...)
	*ver.Message = append(*ver.Message, message) // 新消息插在后面
}
