25.3.18
1. Fundamental Question: What is OOP?
   1. A.B.C <=> A.B().C() <=> C(B(A)), so the member system can be written as function call chain
      1. to emphasize "B belong to A", "C belong to B", we write C_of_B(B_of_A(A))
      2. OOP System is better for user understanding and readability, but it is harder for the language designer to implement
   2. A(x,y).B(z).C(k) <=> C_of_B(B_of_A(A(x, y), z), k)
   3. 像 struct A {field1; field2; field3} 在litex里直接表示成 fn A(field1, field2, field3) 了，fn在litex，或者说在数学里，起到"a collection of objects satisfying certain conditions"的作用
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
   6. 注：不引入oop的话，管理struct和type和set太乱了，对我的编译器设计起到巨大抑制作用。还是需要OOP的。
   7. litex必须要用OOP，否则很多东西没法弄。
      1. 如果不存在同名函数（不同类型的参数列表对应不同的函数），那class就是没意义的。你想同时 让class 没有，然后让函数可以同名，这是做不到的。但数学刚好有无数多的同名函数，比如+，所以必须引入OOP。
2. 数学里函数的返回值是函数很常见
   1. 求导运算，读入函数，输出函数
   2. 函数(运算符) * 既可以作用在数上，也能作用在函数上。比如 f * 2 相当于输入函数f和2，输出函数2f
      1. 正如2可以看成复数，2也能看成函数。2(x) = 2。
   3. 主流编程语言也都支持f(1, 2)(3)(4)这样的写法
   4. 我认为让 $f 也支持链式返回值貌似，即$f(a)(b)(c)，没意义，因为不清楚$f(a)的返回值是什么：难道也是一个prop吗？那$f(a)这个prop是对的还是错的呢？写成$f(a,b,c)貌似也起到了一样的效果
   5. 函数返回值是prop，这个事情本质上是诡异的。函数返回值是返回来一个符号，符号是不能被运行的。但prop是能被运行的。
   6. 函数是能写在()前面的符号，其他性质和obj是一样的

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
obj G Set
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

prop Group(s, idFunc, GroupRingStructOnRealNumbers):
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

obj s GroupType // 自动是集合，同时它可以写s::Id, s::mul
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

obj s set:
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
1. 同一个obj有不同的名字
2. 一个opt1，可能因为它impl了另外一个opt2，而另外的opt可能长相不是opt1，导致最后找不到了
   1. 比如R上+ impl 了 Group 的 *
3. 到底有哪些信息是运行时判断的？哪些是编译时的？
   1. 如果定义prop和fn的时候，我不能从cond里判断出来我可以调用then种的prop和fn，那报错
      1. 这么做是本质的：如果涉及到的运算符是structure of set的运算符，那
   
----------------------------------------------------------------
上述想法已经过期了，正确想法是
1. 现有集合
2. 函数可以定义在集合上
3. 有个关键词叫type，type作用在某个集合上，然后里面放一些东西，放完东西之后说明这个type impl 哪些 struct
如
type real impl GroupRingStructOnRealNumbers: // 定义新类型GroupRingStructOnRealNumbers
    0 impl Group::Id
    + impl Group::Mul
    0 impl Ring::Id
    + impl Ring::Add
    * impl Ring::Mul
    prove:
        ....

// 在这里声明我们从这一行开始，把real视作有结构GroupRingStructOnRealNumbers的
real impl GroupRingStructOnRealNumbers

// 如果未来有个fe，它涉及到的结构有多个，那就手动定义一个type，impl了多个结构，然后继续写。

这么干的好处是，不需要给每个事实都取个名字了：否则你每次传函数参数，一传就是集合，涉及到的opt，一股脑一起传；

我还在怀疑我oop是否有必要加进去.

每次有个新的集合被定义时，你都可以在上面定义新的同名运算。比如在上面定义+。每次你定义完，我都会遍历一遍已经有的同名函数，看看各个里面的cond如果满足了，会不会在你心的同名运算里也满足了。如果满足，那就报错。当然新的cond也不能在任何之前的cond里满足

注意到函数是定义在set上的，而不是定义在type上的。type只是用来说明怎么impl某些struct的

难道说我需要把 定义函数的时候的 涉及到的变量的类型加进来？

struct 是对 不同集合，及其上的运算，的pattern的归总。相当于一种简写。因为你也可以每次写相关命题时，都写成 $Group(s, id, mul)。但每次这么写，一方面累，一方面我searcher不太好search。litex的type是对searcher更好search的一种妥协。

所以本质上type，struct是不必要的。可以用prop和claim模拟出来。但是为了语法糖和让我search更容易（用户不需要给每个事实取个名字），我引入type和struct

e.g. 形式化论断：对于任何集合，对于任何在该集合中的元素，这个元素在这个集合
prop forall_set_forall_element_in_set(s set):
    forall x s:
        x in s

// 用interface。注意到set既可以视作类型，也能视作interface
forall < s set > x s:
    x in s

写在函数里面的cond，应该以set形式写在函数外面
// 不好
fn f(x):
    cond:
        $R(x)
        x > 1
    ...

// 好：注意到这里 相当于 domain_of_f = {x in R | x > 1}。我这里默认下面是<=>关系，而不是 =>。所以不需要写 for all x R 如果 x > 1 那 x in domain_of_f
set domain_of_f:
    domain_of_f subsetOf R
    for x domain_of_f:
        x > 1
    
注：struct除了对set有，“set有没有某member”的要求，还可能对set里的元素有没有一些性质的要求。这些东西统称为struct。set"有没有member"这是相当特殊的性质。这种性质不是普通的用户定义的prop的这种性质，而是内存在解释器里的，工作原理和普通prop不一样。这也是为什么impl这个关键词怪怪的。

fn [T StructName, P StructName] P(a T, b P):
    .... // 全部是then，没cond

如果你想让a有两个struct T1, T2，那对不起，请你定义一个struct T3, T3 包含了T1, T2 的所有性质。我的所有关于参数的性质，全部包含在typeParams, objParams 里了。
上面这样做的意义是，如果 then 里出现的 函数，我默认是 StructName 相关的函数/prop。理论上a和b是不能被作用任何的prop和fn的，但是因为有了T, P 做Struct保障，那它们就能有相关的函数和prop。我们在环境里直接用这些struct相关的函数名。
fn和prop里，正常情况下，都是只有obj有自由度，可以是“任意”。但是有时候我想让set也是“任意”，把一大类的set共有的性质取个名字，放在一起。让set也有自由度。注意到set是很诡异的变量：它虽然是变量，但可以出现在type所在的位置

不能直接完完全全把struct看成go的interface 因为有时候，必须是要知道a和b是同一个集合中的，才能工作。哪怕struct一样，来自的函数可能不一样，那就彻底G了。我们的类型系统要比编程语言这种只需要执行的，要严格一点.
fn P(a StructName, b StructName):
    ... 

因为struct不过是语法糖，实在不行你用prop+claim来写就行。

疑问：如何判断带generics的fn和prop，是否与同名嗲fn和prop冲突呢？特别是一开始定义prop的时候还没证明set impl 某struct，等过了一会再证明。那这个时候必冲突了。
1. 一个选择：runtime的时候再次遍历一下，看看有没有符合。
2. 因为prop里都是关于obj的事实，所以不会影响search

3. 函数重载解析规则
C++ 编译器会根据函数重载解析规则来选择最合适的函数。具体规则如下：

非模板函数优先：如果有一个非模板函数和一个模板函数都能匹配调用，编译器会优先选择非模板函数。

模板特化：如果模板函数有特化版本，且特化版本更匹配调用，编译器会选择特化版本。

模板参数推导：如果只有模板函数匹配调用，编译器会通过模板参数推导来实例化模板函数。

2. 显式指定模板参数
如果希望调用模板函数而不是非模板函数，可以通过显式指定模板参数来强制调用模板函数。

template <typename T>
void foo(T) {
    std::cout << "Template function" << std::endl;
}

void foo(int) {
    std::cout << "Non-template function" << std::endl;
}

int main() {
    foo(42);            // 调用非模板函数
    foo<int>(42);       // 显式调用模板函数
}

或者索性不让任何带generic的prop和fn与其他的fn和prop重名. 我任何这是最合理的。

-----------------------------------------------------
3.19
貌似type这个关键词是没意义的
可以直接拿来 (集合，fc，fc，...) impl struct 来说明它有这个的结构
这样的话，一个集合可以同时impl很多结构，而且也不会打架：因为我验证一条事实FE的时候，我读到你的涉及的函数和prop，然后我只搜到关于这个函数的struct，然后我只搜到关于这样的结构的 generic_opt，然后再得到关于这个generic_opt的generic_prop。所以type在这里不需要出现。就像是同一个type可以impl不同的interface，然后在不同的情况下让它代表不同的interface以传入到不同的函数里。我们这里，如果你要impl一个interface（struct），你需要自己手动地证明一下能impl。然后我们“调用”带有自由度的函数也是和直接call函数名不一样的：我们隐式地搜索你所用的符号涉及到的结构，然后看看满足这种结构的所有的东西的事实，能不能match上你现在所在的地方所需要用的。

这貌似有问题：如果我一个集合上有很多不同的impl一个结构的方式，我去call某个结构相关的事实时，我不能分辨是哪个impl的方式去call了。看来还是只能引入type这个关键词，让同一集合的不同的impl结构的方式去impl一下那个type。

如果你遇到同一个变量所处集合可能有很多的结构，然后我又刚好要用到很多的结构，那你写这样: 虽然这里的a,b,c其实都是一个东西，但是你写成不一样的
prop f< T Struct1, T2 Struct2, T3 Struct3 >(a T, b T2, c T3):
    ...

forall < T Struct1, T2 Struct2, T3 Struct3 > a T, b T2, c T3:
    $f(a,b,c)

obj s set
obj a s
//... 这里让 s impl 了 T1, T2, T3，而 T1, T2, T3 又impl Struct1, Struct2, Struct3
$f(a,a,a) // 这里涉及到的 forall < T Struct1, T2 Struct2, T3 Struct3 > a T, b T2, c T3: 自动定位到了a同时在3个type里，type分别有3个性质，所以能找到

-----
3.20
哪种更好？
1. domain的要求放在cond里
2. 像数学一样，在定义函数前，先把函数的定义域集合给定义好，（或者在定义函数前就把generics定义好一类集合。始终记得generics是prop的语法糖，其实nothing special）。
我觉得2更好
1. cond容易把generics和普通要求，混在一起

哪里会出现generics
1. S 是 R 的子集。是子集这个事情就是generics：因为有很多的R的子集。
2. S 是欧几里得空间，dim(S) = 某个大于1整数
3. S 是 R 中的可测集
4. S 是一个群

貌似把所有的set_struct改名叫interface更合理。
type和set都能出现在litex的参数列表的类型要求里。
虽然它叫interface，但是它有个核心的地方和golang的interface不一样：你不能直接把interface当做一个参数类型传入。你只能在函数头里像写template那样写一下。原因是，有时候你必须要说明一下两个type是出自同一个interface，而不能像go一样，两个type只要都impl一个interface，那就行。

// 出现在<>的是 type-interface pair，不能是set-interface pair
fn f<G Group>(g G, g2 G) G:
    ret = g * g2

// 不能写成下面，因为我想在编译时，就知道你写的 f(a,b) 是不是有问题；万一你传入的a和b压根就是两个集合的，那根本没法运算。我要约束一下你g和g2来自同一个集合（类型）(类型相同，一定来自同一个集合)
fn f(g Group, g2 Group) Group:
    ret = g * g2

最后剩下的golang的struct-type-interface系统和litex的区别：数学里，一个变量可以出现在很多类型里，比如0可以出现在nat, 可以出现在natAsGroup, natAsRing里。golang的解决方法有两个
1. 
type SelfInt int
obj s int = 1
selfInt := SelfInt(s) // 引入新变量
1. 使用接口（interface）或者类型断言
func printValue(s interface{}) {
    switch v := s.(type) {
    case SelfInt:
        // ...
    case int:
        // ...
    }
}
typescript 的解法是
objName as typeName
litex 采用 ts 的做法

嵌入

数学里，嵌入是指把一个集合单射到另外一个集合，同时保持其原有的性质。
1. 集合论的嵌入就是单射。因为集合上没结构
2. 拓扑的嵌入：f: X -> Y, 单射，f是同胚的
3. 代数的嵌入：把代数结构（群环域）单射到另外一个代数结构，保持运算
4. 微分几何：给定两个流形M，N；f:M->N，f是浸入
5. 泛函：保持范数或拓扑结构

数学里的”带有结构的集合嵌入到更大的几何“：用as关键词

类型 A 可以被 as 成更大的类型 B
1. 首先要求一定是单射
2. 其次 B 里的运算可以被A的运算impl（类似类型去impl interface一样） 
3. 在使用as前，你必须要先证明一下你确实可以as
   1. 注意到可能有无数种方法as：比如R中元素嵌入到C里，嵌入方式是x -> 2x。那也保持一切运算
   2. 所以只能是type嵌入到type，不能是set嵌入。因为同一个set有无数种方法嵌入到另外一type

为了方便某个type可以随时加入新的结构（只要新结构没有和已经有同名的旧有结构打架，），我应该像golang一样能随时向type里绑定新结构（用impl来证明这种绑定的正确性）

--------------------
3.21
1. set 的声明
   1. 根据陶哲轩分析1，set只有3种定义方式：
      1. 一个有限集合，集合里是已经声明了的东西
      2. 给定一个集合，取该集合的符合特定条件的子集
         1. 必须先给定一个集合，否则会出现”包含所有集合的集合”这样的悖论
      3. axiom replacement: 有一个prop叫P(x,y)，其中x在集合A中，y任意，那存在一个集合S，它满足：forall y in S, exit x in A s.t. P(x,y) is true
         1. 这样的几何的构造方式，对应函数的值域
   2. 集合之间能运算：交并补
   3. 不是所有东西都是集合，见axiom regularity
   4. 值得一提的是，每当用户声明一个set，我都在环境里赠送给用户一个判断符=。你可以直接用。但是我会认为，同一个obj，出现在不同的集合里，它也是不同的obj。你如果要让他们相等，要么是集合1能impl集合2；要么是你as一下。
   5. 一个obj可以在很多集合里，同时该obj在每个时刻，只被视作在某个集合（类型）里。

// 定义法1
set S {1,2,3}

// 定义法2
set S1 real:
    ret > 0

set S2 nat:
    ret > 0
    ret < 100

// 定义法3
prop P(x S, y S2):
    // ...

exist_prop exist_x_st_P_is_valid(y S2):
    // ? Todo: exist x in S s.t. $P(x,y)

set S3 exist_x_st_P_is_valid

2. type 的声明
   1. (set, opts, props) 一起impl 一个type
      1. prop也是impl：比如说 <, > 这种，只要有结构，它可能有不同的意思，但是运算符号的性质可能是共通的
   2. type impl interface
      1. 一个时刻，type可以impl很多的interface
   3. 一个时刻，一个obj只能出现在一个type里
   4. 类型被看做集合，但是如果 set1 impl type1，那type1和set1被视为不同集合

3. interface：一族type
   1. type->interface本质上是语法糖，是为了让litex去search fact的时候能实现自动（如果不引入这个语法糖，那每次用户都要给一个事实取名了）。
   2. interface 中的函数的一大特点是，很多函数都可能可以满足interface中的对该函数的要求。比如吃int上可以定义很多群结构：正常的+；取余数+；它们都符合群的定义。
      1. 这也是为什么要引入type：不能直接建立set 和 interface 之间的关系：因为同一个set，可能有很多实现interface的方法。必须有个中间层type，来说明一下是以哪种方法实现的。

set R
    type RAsGroup R implements Group: // 表示 集合R上的Type RAsGroup implement  interface叫Group
    __add__ impl __mul__
    0 impl id
    __neg__ impl __inverse__
R impl RAsGroup // 之后 R 会被默认以RAsGroup的方式impl Group。于是Group相关的事实可以被运用在R上

注：在golang和Java中，一个类(type)可能implement很多interface；implement的方式是：这个类实现了这个interface所有对应的函数。litex里，一个set可能实现很多type，一个type可能实现很多interface；这么看来一个set可能以很多方式implement一个interface。litex的 type implement interface 的方式是：这些函数和prop的相关事实，和interface要求的刚好”对上“

值得一提的是，符号以下条件的fn可能有无数个
// 定义一个 返回值 大于0 的函数
fn f(x R) R:
    self > 0

如何search事实: 
1. 相等型事实
f(a,b)(c,d) = g(e,f) 是否成立？
know f(a,b) =g 
e = c
f = d

对应 e 和 c，f和d
   1. 对上了，则考虑 g 和 f(a,b) 是否相等
      1. g = f(a,b) 作为函数相等，则相等
      2. 如果不等，那直接比较 f(a,b)(c,d) = g(e,f) 是否成立
   2. 没对上，则考虑 f(a,b)(c,d) = g(e,f) 作为整体是否相等
      1. 相等，则OK
      2. 不相等，则确实不可能相等

1. $g(a,b) 是否成立?
   1. 看看有没有已知的事实$g(c,d)，c和a相等，b和d相等
   2. 看下有没有h和g等价；如果h和g等价，$h(a,b)成立，那就成立
      1. 我可能不想引入iff这个关键词；请你全部写成 
        forall x A, y B:
            $g(x,y) // 这里也可以看到，cond是必要的：否则每次都在外面定义一个集合，太烦了
            then:
                $h(x,y)

        forall x A, y B:
            $h(x,y)
            then:
                $g(x,y)
        然后你先证明$h(a,b)，然后手动说明一下 $g(a,b)
        或许我可以引入iff这个语法糖，让上面的操作（search）自动进行

3.22
zzy
1. interface 之间的继承
   1. semi-group impl group
   2. 不只是set之间的继承：R to C
   
know prop fact_about_a_group(s set, id fn, inv fn, __mul__ fn, x s, y s, z s):
    cond:
        $Group(s,id,inv,fn)
    then:
        x * y * z = x * (y * z)


int impl IntAsGroup // 从这个时刻开始，把int看成type IntAsGroup
IntAsGroup impl Group
know forall < G Group > x G, y G, z G:
    x * y * z = x * (y * z)

// ...
1 * 2 * 3 = 1 * (2  * 3)

2 > 1

add(1,2) + add(2,3) > 1000

exist_prop exist_nat_less_than(n Nat):
    have:
         obj m Nat
    then:
        m < n

know forall n Nat:
    cond:
        n > 0
    then:
        $exist_nat_less_than(n)

$exist_nat_less_than(100) // As a specific factual expression, it is true.
have m Nat: $exist_nat_less_than(2)   // Introduce new object, m, to current proof environment

exist_nat_less_than(100) = (1 = 1) // 实现这个功能没有意义，同时会混淆=的语义

fn exist_nat_less_than

exist_nat_less_than(100) > 2

目前先送给用户数归法这个prop，日后实现prop generator：prop generator 和 普通prop的本质不同是，prop generator能读入fact作为参数

prop 能读入prop，但是fn不能？
fn：按集合论的定义，不涉及到prop；但是prop貌似需要？因为本质上prop和fn就不是一种东西，所以prop能读入prop，fn不能读入prop，也没有破坏对称性
1. 如果你把prop放在type里（比如你把<放入类型），那相当于也就是往prop里传prop参数
2. 如果你允许prop能读入prop，那一些事实的实现会非常容易，比如数学归纳法

prop mathematical_induction(p prop):
    $p(0)
    forall n nat:
        $p(n)
        then:
            $p(n+1)
    then:
        forall n nat;
            $p(n)

know forall p prop:  // 这里有个怪异的地方：forall我会认为你输入的，都是一个集合里的东西，但是你这里的prop，代表的是一个集合吗？？？需要思考一下会不会导致严重问题
    $mathematical_induction(p)

如果说引入新的keyword：
prop_prop mathematical_induction(p prop):
    $p(0)
    forall n nat:
        $p(n)
        then:
            $p(n+1)
    then:
        forall n nat;
            $p(n)

know forall_prop  p prop: 
    $mathematical_induction(p)

// mathematical induction 也能被当做prop被传到prop prop里
prop_prop Q(p prop):
    //...

$Q(mathematical_induction)

思考一下如果我不允许函数和prop的名字冲突，那我$是否必要呢??

25.3.23
1. 我们litex不像lean一样，先定义群再定义nat。我们可以随时定义任何集合（比如nat），然后说明nat的一些操作impl了群的结构

25.3.24
有三种定义集合的方法
1. 有限个obj
2. {x in S| Q(x)}
    forall x S:
        Q(x)
    prop 偶数(x R):
        x in nat // 这里相当于取定义域是 {x in R| x in nat}

    这里的S对应x in S, condition Q(x) 对应|右边的Q(x)

3. {x in A| exist y in B s.t. P(x,y) 成立}
    forall x A:
        exist_P_x_y_y(x,y)
    // 定义：y在函数f的值域里: f: x in A -> y in B
    prop exist_x_fx_equals_y(y B):
        var x A
        then:
            f(x) = y

这是很本质的观察：
1. 2.中出现了forall
2. 3.中出现了exist；这种写法和y是f(A)的值域中的元素对应上了
3. 1. 中是最常见的定义set的方式

Set 的几大功能
1. 作为参数类型
    forall x Set
2. 作为Generics中的type的interface
    forall < S Set > x S
3. 内置了in函数
    x in A
4. 任何type都能视作set
    type RAsGroup R
    1 in RAsGroup   // 自动检查是否1在集合RAsGroup所处于的集合R里
5. 只有set上能绑定函数，而不是type上
    因为我会认为type是语法糖，而按照数学的基本定义，函数就是定义在set上的

还缺什么语法
1. type def
2. interface def
3. prove type impl interface
4. exist def
5. have exist: introduce new object
6. prove obj satisfy exist factual expression

还缺什么语义
不带Generics
1. =的验证：等号的验证需要和事实的推理的验证独立开,即符号相等的验证，和forall，specific fact 的验证是很不一的
   1. param的比较: a = b, f(a) = f(b)
   2. 函数作为整体的比较: f(a) = g, f(a)(b) = g(b)
~~2. prop之间的等价，不用=。即我不写prop=prop。我只写fn=fn，obj=obj~~
   ~~1. 我甚至也不想引入iff：你直接把iff的意思全部写出来就行~~
3. forall 如何工作
   1. 最大问题：怎么search
      1. forall a A, b B:
            Q(a,b)
      2. forall a A, f fn:
            Q(a, f(a))
      3. 相当严重的问题：如果传入的东西里有prop怎么处理（我暂时先只考虑1.,2.）
         1. forall a A, f fn, p prop:
                p(a,f,p)
   2. forall或者fn里，我的“自由变量”如何当做其他什么东西的同名函数
4. fn相关
   1. fn对传入的参数做检查
      1. fn的参数列表里能写type，也能写set。但我建议你写set
         1. 我或许应该禁止用户写type。
      2. know f(a) = 2
         1. 如果a压根不满足f的cond，那用户这样写，我是不是要警告一下用户呢
   2. 特别是，用forall 进行search的时候，我把当前的参数代入到已知的forall事实里，这个时候各种可能的难点就出来了。具体可能碰到哪些问题需要思考一下
   3. 疑问：我要引入fn的类型吗？
      1. 貌似不用：如果我传入了不符合规定的参数，那我会报错的。至少说我不会让你通过
   4. 函数只能读入集合和函数（函数本身也是一种集合），绝对不能读入prop，也不能返回prop
   5. 想让函数有某种Generic性质，即读入“任何符合类型的集合 的参数”，而不是读入“某个集合参数”，那就用interface
~~5. prop 本质上和 fn 是不一样的~~
   ~~1. prop：起到普通PL的函数的作用，输出值：true, false, unknown, error~~
   ~~2. fn: 起到C中的struct的作用，把一符号放在一起形成新符号~~
   1. prop能读入prop作为参数，虽然我现在不太想实现这个功能
      1. 我可能先送给用户数归法这个prop generator。但是让用户自己定义prop generator我可能暂时不想这么干.
1. 内置集合（类型）
   1. nat
      1. real, int 都是从nat来的。这些可以由用户自定义
   2. rational
      1. rational也能由nat诱导而来，所以也只要用户自定义就行。但是像1.2这种数是内置在系统里的，所以rational只能由系统送给用户
   3. nat rational
      1. +-*/的定义，是需要内置的。因为只有1,2.3这种obj，它的字面量是有意义的，其他东西的字面量都没意义。只有1+1=2这种，需要我解释器帮你验证
      2. nat和rational这种，一下子引入了无数多的obj，这也是用户一个个引入普通obj所做不到的
   4. set
      1. in
      2. 作为interface，集合，
2. relational和FnRet函数的分离；relational spec fact 和 func spec fact 的分离
3. 超级大问题：search和store时如何compare
   1. 需要仔细想一想
4. as
   1.  as(obj, typeName/setName) 之所以可以读入setName是因为一个obj可以被放在很多的集合里
5.  subset of
    1.  把一个集合视作另外一个集合的子集
    2.  比如R可以看成C的子集；nat看做rational的子集
    3.  这种“看成子集“，怎么证明呢，有哪些语义方面的问题？
        1.  语义：比如我现在fn是读入参数为C的，那我输入1，应该也要能通过
6. 定义set上的builtin opt：比如__add__，语法咋样
7. 貌似还不能parse 1 < b

Generics（interface）的语义
1. 过于困难，之后再说
   1. 困难之处在于，不知道怎么search。怕和正常的语法语义有冲突
   2. 另外一大困难是，我在证明关于Generics的性质时，我怎么去做证明。我这时候开的局部环境和正常的大环境是截然不同的：大环境是具体的set，而Generic 环境里，我不知道你所谓的集合导致是哪个集合
   3. 要把 prop 做成type的member：因为=也是跟着type的。
   4. forall < G Group::Group > g G, g2 G:
        G::Abel(g, g2) // 自动判断出是g所属的G的Abel函数
2. generic 声明或许也能写成这样
prop Q(S Group, g1 S, g2 S):
    //...
这时候S也能从g1,g2推理出来，无非是 prop Q < S Group >(g1 S, g2 S) 换种写法

3. 注意到interface真的只是set+opt+prop的语法糖：当我输入一条concrete的事实时，我新生成的事实是，关于最最原始的set+opt+prop的事实。
4. 如何定义impl
   1. 有时候impl需要作为factual expression出现

实现的目的是做成语法糖的功能
1. interface impl interface
   1. 比如群impl半群
   2. 这相当于是语法糖的语法糖：interface是set+opt+prop的语法糖；interface impl interface 是更强的语法糖：比如半群相关的事实，当我现在是群是，立刻满足，而不需要我手动去再说明一下。即任何关于一个群的事实，我都会拿来关于半群的事实去验证一下他。
2. commutative, associative
   1. 只有你声明过了，同时我检查过了你说它有这些性质确实都有了，那我会在检查的时候帮你用可能的情况都检查一下。你颠倒着写不要紧。

注：xxx of yyy 唯一出现的地方是，member of interface。其他地方一律不会出现。那这样一来，因为任何generics函数里，我都会写成 prop Q< S InterfaceName >(x S) ，然后涉及到的函数也是写成 S::__add__ 这种，所以不会导致需要连续2个::的情况：packageName::interfaceName::memberName是不会有的，只有typeThatImplInterface::memberName

3.25
如何声明set
严格的方法：对应3个定义方式
    定义法1：有限集合 
        set s :
            1,2,a,b // 把所有的元素写在第二行
    法2: S 是 S2的子集，满足一些性质(可以是普通性质，可以是存在性质)
        set s s2:
            P(inst)
            exist_p(inst)
    法3：其他集合的交并补
        set s = s1 union s2 intersection s3
不严格：直接定义(现在先这样定义；未来成熟之后，用严格定义法引入新的定义方式。因为我也确实不知道怎么严格定义“矩阵集合”这样的集合)
var nat_matrix_2_2 set
fn nat_matrix_2_2::at(a nat, b nat) nat:
    cond:
        0 < a < 2
        0 < b < 2
        
3.26
interface impl interface。或者说有 “xx的yy” 的情况，需要引入 xxx::uuu::yyy, 单独一个::不够了。比如我要实现 Group::Group的mul，
注意到， 默认右边的  函数名，对应的是 interface 名的那个需要被impl的函数，就能避免这个问题
// 群是半群
prove < G Group::Group > G impl Group::SemiGroup:
    G::__mul__ impl __mul__  // 默认mul指代的是SemiGroup的mul // 那或者说左边的 __mul__ 也是默认的，不用写 G::__mul__了
如何让两个type，形成一个语法糖，能impl一个新的东西呢: 不太能，要么你定义新的type把原来的这两个type包裹进去；要么全部统一用prop来一个个地表示满足这些性质的东西怎么搞

3.28
1. 为了统一性，让所有的atom都形如pkgName::name 我让用户定义在某个type上的__add__时，定义方式是__add__typeName__ 之后你想把这个函数作为参数传递也是用这个名字
2. 数学是一层又一层的抽象。人类做抽象的方法其实是只是在某几个方向做抽象，还有大量的方式没做
   1. 比如人们做抽象，经常是 keyword1 -> keyword2 -> keyword3 ... 这样一层层做；但逻辑上，keyword3 -> keyword1 -> keyword2 -> ... 可能也是能通过的。之所以后者不受重视，是因为不能对应到现实生活中。

4.1
1. forall 中要不要添加新的field：when
now
forall x A:
    dom:
        $p(x)
        $t(x)
    then:
        $q(x)
?
forall x A:
    dom:
        $p(x)
    when:
        $t(x)
    then:
        $q(x)
dom 和 when 分离：一个专门表示定义域，一个表示在定义域基础上，还有额外要求
写在一起，在语义上，本质上是一样的，但是写一下貌似更分明？还是说确实有语义上的细微不同导致我必须分离他们？
这样一大好处是，可以引入iff
forall x A:
    dom:
        $p(x)
    when:
        $t(x)
    iff:
        $q(x)
2. prop
prop x A:
    $p(x)
    then:
        $q(x)
vs
prop p(x A):
    $p(x) // dom
    iff: // dom 上的额外要求. dom满足时 p(x)则q(x), t(x), q(x) && t(x) 则 p(x)
        $q(x)
        $t(x)
3. 如果把forall里加iff，会发生什么
完整版
forall x A:
    dom:
        DOM
    when:
        WHEN
    then/iff:
        THEN/IFF

略去when
forall x B:
    DOM
    then/iff:
        THEN/IFF

全略去
forall x B:
    THEN/IFF

巨大问题：when里必须要全是 specFact，否则因为 THEN/IFF 要求你全是SpecFact，而when需要和iff有语义上的并行关系，所以WHEN也必须spec

litex 0.2 前不加入这个功能


25.4.5
1. 本项目是regex matcher。而且是超级加强版，用户可以自己定义 regex的特殊符号（用来match 自由变量），而只是regex里面的只有 []*+ 这种，它们能自己定义 litex 里面的 特殊符号和相应match规则。
   1. 本质上 这些特殊符号就是 forall x X: conditions then: 某特殊符号能match这个x
   2. 普通regex matcher 是 静态的代码去match（match的规则固定，写在了解释器里），而我因为要让用户用到自己之前已经知道的事实，所以是 动态环境下的match
      1. 有点类似 struct 静态写好了field名；dict能让用户在runtime随时改变field名

4.7
1. python 的 repl 里，python是怎么做到，如果一个指令执行到一半发现有点问题，虽然执行到一半已经对环境有点破坏了，但是还是能回退到原来好的环境
   1. 用户错误分两种
      1. 语法错误
         1. 这种错误不会影响env，所以无所谓
      2. runtime错误
         1. 这种错误可能会影响env（比如know 10 个事实，第8个事实在被保存的时候出错了，那前几个事实已经存好了）
   2. Python 本身 不提供自动回滚机制
      1. 为什么 Python REPL 不自动回滚？
      2. 性能考虑：记录所有变量修改成本高。
      3. 复杂性：Python 允许任意副作用（如文件操作、网络请求），无法自动回滚。
      4. 设计哲学：Python 采用 "请求原谅比请求许可更容易"（easier ask for forgiveness then permission） 风格，鼓励显式错误处理。
   3. 如果用户在repl写litex的时候，产生了runtime error，那我直接把当前环境全部停掉，让用户rerun整个项目
   4. 不过litex的好处是，上一时刻的env和下一时刻的env其实是分的很开的。我甚至可以每次运行一个新的事实的时候，建立一个新的env，让这个env只管这一次语句的执行
      1. 甚至说我还可以让新的env的执行，如果执行ok了，那就让它merge到上一层env里

25.4.9
第一个能“逻辑完备”地运行的版本
下面这个东西能正常运行，而且不会iff死锁。因为我最多找2次forall类型事实，不会互相找
prove:
    know:
        // Define: p(x) iff forall y: cond(y) => result(x,y)
        
        // p(x) => (forall y: cond(y) => result(x,y))
        forall x B, y A:
            $cond(y)
            $p(x)
            then:
                $result(x,y)
        
        // (forall y: cond(y) => result(x,y)) => p(x)
        forall x B:
            forall y A:
                $cond(y)
                then:
                    $result(x,y)
            then:
                $p(x)

    prove: // OK
        know $p(1)
        forall y A:
            $cond(y)
            then:
                $result(1,y)

    when:
        forall y A:
            $cond(y)
            then:
                $result(1,y)
        then:
            $p(1)    