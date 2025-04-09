package litex_global

func Setup() {
	initSymbolSet()
}

var symbolSet map[string]bool // 存储所有符号
func initSymbolSet() {
	symbolSet = make(map[string]bool)
	for _, symbol := range KeySymbolSlice {
		symbolSet[symbol] = true
	}
}
