1. curXXX means current XXX, like curEnv means currentEnv
2. Def means definition, like DefPropStmt means Definition of Proposition Statement
3. exec means executor
4. ver means verifier
5. stmt means statement
7. prop means proposition
8. obj means object
9. fn means function
11. num means number
12. str means string
13. msg means message
14. sig means signal
15. numExprFc means numeric expression first citizen
16. fc means first citizen: it is an atom or a function (a function in Litex is a first citizen which uses a brace to wrap its parameters). It is a noun in Litex, or math. It is what propositions (verbs) operates on. A function is not a verb.
17. cmp means compare, package cmp is for comparing two fc. It compares the fc literally, if they are the same, it returns true, otherwise it returns false. If the fc is a number or number expression, it will be simplified first, then compared. It's noteworthy that main logic of this package is independent of all other packages and mimics how human compares two things.

If you are pretty sure your naming explains everything well and the variable only affects one small part of the code, you violate the above rules. However, if the variable affects multiple parts of the code, you should follow the above rules.