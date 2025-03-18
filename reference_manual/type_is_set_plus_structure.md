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

package GroupTheory

struct Group:
    fn id(s)
    fn mul(x,y)
    fn inv(x)

    know:
        forall x:
            x in this
            then:
                mul(x , id(this)) = mul(id(this), x)
                mul(x, inv(x)) = mul(inv(x), x) = id(this)
        forall x,y:
            x in this
            y in this
            then:
                mul(mul(x, y),z) = mul(x,mul(y,z))
                
fn Id(s):
    s is Set
fn Inv(x)

// 引入一个集合，这个集合有群结构
var G Set
know G impl Group:
    Id impl Group::id
    \_\_mul\_\_ impl Group::mul
    Inv impl Group::inv

// ??如何处理builtin Operator overload
// ??比如这里 \_\_mul\_\_(G) 表示，函数mul读入了参数G，返回一个新函数，这个函数impl Group::mul

我们在这里可以看到神奇的一点。Id看起来不像是函数，因为它的定义域是不固定的，任何参数都能传到这个Id的参数列表里。这简直就是超级generics：根本不管type，直接用。相当于超级函数名重载。它像是一个能放入任何东西的标记符号，或者说类似C里的struct，而不是函数。
如果不在 fn 在定义的时候就加好cond，那就回出现上述情况

// 另外一种写法
package GroupTheory

fn Id(s):
    s is Set

fn Inv(x)
fn mul(x,y)

prop Group(s, idFunc, mulFunc):
    // 其实这三个没必要：x in s 已经说明s是集合；mulFunc(x,y)说明mulFunc是fn
    s is set
    idFunc is fn
    mulFunc is fn

    forall x:
        x in s
        then:
            mulFunc(x , idFunc(this)) = mulFunc(idFunc(this), x)
            mulFunc(x, inv(x)) = mulFunc(inv(x), x) = idFunc(this)
    forall x,y:
        x in s
        y in s
        then:
            mulFunc(mulFunc(x, y),z) = mulFunc(x,mulFunc(y,z))
    
    then:
        // 这里的impl表示，Id 和 idFunc 在一样的定义域上，是等价的。如果x只在Id定义域，不在idFunc，那就G了
        idFunc impl Id
        mulFunc impl mul

// 如何说 (G, F1, F2) impl Group

疑难杂症:如果我也像lean一样，让用户自己给每个事实都取个名字，那我日子会好过多了，因为我不用search了
比如下面这个，如果我能传：集合，id函数，mul函数，那我就舒服多了。
这里有硬伤：then 里面的表达式，没有涉及到id(mul可以直接得到；s可以从x所在集合得到；id？？？)
claim factName(s,id,mul):
    $Group(s, id, mul)
    then:
        forall x, y:
            x in s, y in s
            then:
                mul(mul(x, y),z) = mul(x,mul(y,z))
    prove:
        mul(mul(x, y),z) = mul(x,mul(y,z))

如果有OOP的话，上述问题较好解决：我定义一个东西叫type(set+structure),type里保存了一些field，这些field能和prop Group里的要求对应。如果把相关的信息绑定在变量上，那我search就可以运行了，不需要用户自己写claim啥的了

type GroupType {
    fn Id(x)
    fn mul(x,y)
}
know forall s:
    s impl GroupType
    then:
        $Group(s, s::id, s::mul)

var s GroupType // 自动是集合，同时它可以写s::Id, s::mul
know $Group(s, s::Id, s::mul)

// 于是上述的claim就不需要写成prop格式，能执行局调用了
forall x,y:
    type_of(x) impl GroupType
    type_of(x) = type_of(y)
    then:
        type_of(x)::mul(type_of(x)::mul(x, y),z) = type_of(x)::mul(x,type_of(x)::mul(y,z))

// 另外一种写法：不用OOP
fn fn_as_group_mul(s):
    s is set
    then:
        ret is fn
fn fn_as_group_id(s):
    s is set
    then:
        ret is fn

var s set:
    know $Group(s, fn_as_group_mul(s), fn_as_group_id(s))

// 或者索性把Group定义成下面的形状
prop Group(s):
    s is set
    fn_as_group_id(s) is fn
    fn_as_group_mul(s) is fn

    forall x:
        x in s
        then:
            fn_as_group_mul(s)(x , fn_as_group_id(s)()) = fn_as_group_mul(s)(fn_as_group_id(s)(), x)
            fn_as_group_mul(s)(x, inv(x)) = fn_as_group_mul(s)(inv(x), x) = fn_as_group_id(s)()
    forall x,y:
        x in s
        y in s
        then:
            fn_as_group_mul(s)(fn_as_group_mul(s)(x, y),z) = fn_as_group_mul(s)(x,fn_as_group_mul(s)(y,z))
    
    then:
        fn_as_group_id(s) impl Id
        fn_as_group_mul(s) impl mul

------------------------------------------------

// 第三种写法
package GroupTheory

fn Id(s):
    s is Set

fn Inv(x)
fn mul(x,y)

prop isGroup(s):
    s is set
    then:
      forall x:
        x in s
        then:
            mul(x , id(s)) = mul(id(s), x)
            mul(x, inv(x)) = mul(inv(x), x) = id(s)
      forall x,y:
        x in s
        y in s
        then:
            mul(mul(x, y),z) = mul(x,mul(y,z))

// 这时候如何说(s,id,f)是群
know $isGroup(s), id = Id, f = mul


// 第一种写法更合理
Search 时，需要处理同名的情况
1. 同一个var有不同的名字
2. 一个opt1，可能因为它impl了另外一个opt2，而另外的opt可能长相不是opt1，导致最后找不到了
   1. 比如R上+ impl 了 Group 的 *
3. 到底有哪些信息是运行时判断的？哪些是编译时的？
   1. 如果定义prop和fn的时候，我不能从cond里判断出来我可以调用then种的prop和fn，那报错
      1. 这么做是本质的：如果涉及到的运算符是structure of set的运算符，那