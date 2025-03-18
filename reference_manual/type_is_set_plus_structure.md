25.3.18
1. Fundamental Question: What is OOP?
   1. A.B.C <=> A.B().C() <=> C(B(A)), so the member system can be written as function call chain
      1. to emphasize "B belong to A", "C belong to B", we write C_of_B(B_of_A(A))
      2. OOP System is better for user understanding and readability, but it is harder for the language designer to implement
   2. A(x,y).B(z).C(k) <=> C_of_B(B_of_A(A(x, y), z), k)
   3. 像 struct A {field1; field2; field3} 在litex里直接表示成 fn A(field1, field2, field3) 了，fn在litex，或者说在数学里，起到"a collection of variables satisfying certain conditions"的作用
      1. C最初也没struct关键词。可以自己设置一个void**来存不同类型的东西，比如我们脑子里记住第0位表示field1 *,第1位表示field2 *
   4. 由此可见，litex根本不需要实现oop
   5. litex不实现oop的好处坏处中立
      1. 好处
         1. 极大的好处：解释器好写多了：作为个人项目，litex不能太复杂了。和C一样复杂已经是极限
         2. 不会和小数打架
         3. 
      2. 中立
         1. 虽然编程里经常OOP，但是数学里没有。所以可能引入OOP反而让用户在不该用OOP的地方用它
         2. litex里函数某种程度上起到了OOP的作用：把其他符号放在一起
      3. 坏处
         1. 不能用到现代的编程技术
2. 数学里函数的返回值是函数很常见
   1. 求导运算，读入函数，输出函数
   2. 函数(运算符) * 既可以作用在数上，也能作用在函数上。比如 f * 2 相当于输入函数f和2，输出函数2f
      1. 正如2可以看成复数，2也能看成函数。2(x) = 2。
   3. 主流编程语言也都支持f(1, 2)(3)(4)这样的写法
   4. 我认为让 $f 也支持链式返回值貌似，即$f(a)(b)(c)，没意义，因为不清楚$f(a)的返回值是什么：难道也是一个prop吗？那$f(a)这个prop是对的还是错的呢？写成$f(a,b,c)貌似也起到了一样的效果
   5. 函数返回值是prop，这个事情本质上是诡异的。函数返回值是返回来一个符号，符号是不能被运行的。但prop是能被运行的。
   6. 函数是能写在()前面的符号，其他性质和var是一样的

package Group
fn id(G):
    $Set(G)
