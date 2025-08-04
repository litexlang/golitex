## Python API

### Run REPL in python

```py
# Run REPL in python
import litex
runtime = litex.Runtime() # Similar to writing `litex` in terminal
msg, ok = runtime.run(
`let a R:
    a = 1
a = 1`
)

print(msg)
print(ok)
```

### Run a file in python

```py
import litex
runtime = litex.Runtime()
msg, ok = runtime.run("import FILENAME.lix")
print(msg)
print(ok)

# You can continue to run more code after running a file
msg, ok = runtime.run("a = 1")
print(msg)
print(ok)
```

### Run a repo in python

```py
import litex
runtime = litex.Runtime()
msg, ok = runtime.run_repo("import REPO_PATH as REPO_NAME")
print(msg)
print(ok)
```