GOOS=windows GOARCH=amd64 go build -o ./binary/litex_windows.exe main.go

GOOS=linux GOARCH=amd64 go build -o ./binary/litex_linux main.go

GOOS=darwin GOARCH=amd64 go build -o ./binary/litex_mac main.go