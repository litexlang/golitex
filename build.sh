GOOS=windows GOARCH=amd64 go build -o ./binary/windows_litex.exe main.go

GOOS=linux GOARCH=amd64 go build -o ./binary/linux_litex main.go

GOOS=darwin GOARCH=amd64 go build -o ./binary/mac_litex main.go