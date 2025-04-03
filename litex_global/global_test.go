package litexglobal

import (
	"log"
	"runtime"
	"testing"
)

func TestRuntimeGetFuncName(t *testing.T) {
	pc, _, _, _ := runtime.Caller(0)
	fcName := runtime.FuncForPC(pc).Name()
	log.Println(NewErrLinkAtFunc(nil, fcName, "").Error())
}
