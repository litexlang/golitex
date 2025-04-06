package main

import (
	"fmt"
	litex_sys "golitex/litex_sys"
)

func main() {
	msg, err := litex_sys.ExecFileReturnString("./litex_code_examples/litex_as_regex_matcher.lix")
	// msg, err := litex_sys.ExecString("a < b")
	if err != nil {
		fmt.Println(err.Error())
	}
	fmt.Println(msg)
}
