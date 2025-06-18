package litex_global

import (
	"math/rand"
	"time"
)

const (
	letterBytes   = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
	letterIdxBits = 6                    // 6 bits to represent a letter index
	letterIdxMask = 1<<letterIdxBits - 1 // All 1-bits, as many as letterIdxBits
)

// RandomString generates a random string of specified length
func RandomString(length int) string {
	// Initialize random seed
	rand.New(rand.NewSource(time.Now().UnixNano()))

	b := make([]byte, length)
	for i := range length {
		b[i] = letterBytes[rand.Intn(len(letterBytes))]
	}
	return string(b)
}
