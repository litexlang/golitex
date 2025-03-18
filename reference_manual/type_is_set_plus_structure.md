25.3.18
1. Fundamental Question: What is OOP?
   1. A.B.C <=> A.B().C() <=> C(B(A)), so the member system can be written as function call chain
      1. to emphasize "B belong to A", "C belong to B", we write C_of_B(B_of_A(A))
      2. OOP System is better for user understanding and readability, but it is harder for the language designer to implement
   2. A(x,y).B(z).C(k) <=> C_of_B(B_of_A(A(x, y), z), k)
   3. 像 struct A {field1; field2; field3} 在litex里直接表示成 fn A(field1, field2, field3) 了，fn在litex，或者说在数学里，起到"a collection of variables satisfying certain conditions"的作用
      1. C最初也没struct关键词。可以自己设置一个void**来存不同类型的东西，比如我们脑子里记住第0位表示field1 *,第1位表示field2 *
   4. 由此可见，litex根本不需要实现oop
2. 

package Group
fn id(G):
    $Set(G)
