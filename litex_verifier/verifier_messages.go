package litexverifier

import "fmt"

func (e *Verifier) successMsg(stmtString, storedStmtString string) {
	message := fmt.Sprintf("[true]\n%v\n[verified by]\n%v", stmtString, storedStmtString)
	*e.Message = append([]string{message}, *e.Message...) // 新消息插在前面
	// *e.Message = append(*e.Message, message) // 新消息插在后面
}

func (e *Verifier) unknownMsg(format string, args ...any) {
	message := fmt.Sprintf(format, args...)
	*e.Message = append([]string{message}, *e.Message...) // 新消息插入到最前面
	// *e.Message = append(*e.Message, message) // 新消息插在后面
}
