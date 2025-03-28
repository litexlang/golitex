package litexverifier

import "fmt"

func (ver *Verifier) successMsg(stmtString, storedStmtString string) {
	message := fmt.Sprintf("[true]\n%v\n[verified by]\n%v", stmtString, storedStmtString)
	*ver.Message = append(*ver.Message, message) // 新消息插在后面
}

func (ver *Verifier) unknownMsg(format string, args ...any) {
	if ver.round1() {
		message := fmt.Sprintf(format, args...)
		*ver.Message = append(*ver.Message, message) // 新消息插在后面
	}
}
