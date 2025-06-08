# Future Features

1. postfix notation !
Usage: function_name! makes the function_name from a fn (params paramSets) ret to a function to fn (functional params with ret paramSets)
e.g. integral(id +! id) means : + is function from real to real, and id is function from real to real, so integral(id +! id) is function from real to real. id! now takes a function from real to real, and returns a function from real to real.

2. algo
Usage: use user-defined algorithm to prove a statement. This is useful when a proposition is very nested, and the proof is very long with a fixed pattern.
e.g. is_continuous(id *! (id+! id) +! id), here we must use continuous function under arithmetic operations is still continuous to prove the statement. However, there are many nested layers and Litex only handles 2 layers of "forall" for you. You must use a user-defined algorithm to prove the statement.