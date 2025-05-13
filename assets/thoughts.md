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
   4. 我认为让 f 也支持链式返回值貌似，即f(a)(b)(c)，没意义，因为不清楚f(a)的返回值是什么：难道也是一个prop吗？那f(a)这个prop是对的还是错的呢？写成f(a,b,c)貌似也起到了一样的效果
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
    Group(s, id, mul)
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
        Group(s, s::id, s::mul)

obj s GroupType // 自动是集合，同时它可以写s::Id, s::mul
know Group(s, s::Id, s::mul)

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
    know Group(s, fn_as_group_mul(s), fn_as_group_id(s))

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
know isGroup(s), id = Id, f = mul


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

struct 是对 不同集合，及其上的运算，的pattern的归总。相当于一种简写。因为你也可以每次写相关命题时，都写成 Group(s, id, mul)。但每次这么写，一方面累，一方面我searcher不太好search。litex的type是对searcher更好search的一种妥协。

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
        R(x)
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
    f(a,b,c)

obj s set
obj a s
//... 这里让 s impl 了 T1, T2, T3，而 T1, T2, T3 又impl Struct1, Struct2, Struct3
f(a,a,a) // 这里涉及到的 forall < T Struct1, T2 Struct2, T3 Struct3 > a T, b T2, c T3: 自动定位到了a同时在3个type里，type分别有3个性质，所以能找到

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
    // ? Todo: exist x in S s.t. P(x,y)

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

1. g(a,b) 是否成立?
   1. 看看有没有已知的事实g(c,d)，c和a相等，b和d相等
   2. 看下有没有h和g等价；如果h和g等价，h(a,b)成立，那就成立
      1. 我可能不想引入iff这个关键词；请你全部写成 
        forall x A, y B:
            g(x,y) // 这里也可以看到，cond是必要的：否则每次都在外面定义一个集合，太烦了
            then:
                h(x,y)

        forall x A, y B:
            h(x,y)
            then:
                g(x,y)
        然后你先证明h(a,b)，然后手动说明一下 g(a,b)
        或许我可以引入iff这个语法糖，让上面的操作（search）自动进行

3.22
zzy
1. interface 之间的继承
   1. semi-group impl group
   2. 不只是set之间的继承：R to C
   
know prop fact_about_a_group(s set, id fn, inv fn, __mul__ fn, x s, y s, z s):
    cond:
        Group(s,id,inv,fn)
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
        exist_nat_less_than(n)

exist_nat_less_than(100) // As a specific factual expression, it is true.
have m Nat: exist_nat_less_than(2)   // Introduce new object, m, to current proof environment

exist_nat_less_than(100) = (1 = 1) // 实现这个功能没有意义，同时会混淆=的语义

fn exist_nat_less_than

exist_nat_less_than(100) > 2

目前先送给用户数归法这个prop，日后实现prop generator：prop generator 和 普通prop的本质不同是，prop generator能读入fact作为参数

prop 能读入prop，但是fn不能？
fn：按集合论的定义，不涉及到prop；但是prop貌似需要？因为本质上prop和fn就不是一种东西，所以prop能读入prop，fn不能读入prop，也没有破坏对称性
1. 如果你把prop放在type里（比如你把<放入类型），那相当于也就是往prop里传prop参数
2. 如果你允许prop能读入prop，那一些事实的实现会非常容易，比如数学归纳法

prop mathematical_induction(p prop):
    p(0)
    forall n nat:
        p(n)
        then:
            p(n+1)
    then:
        forall n nat;
            p(n)

know forall p prop:  // 这里有个怪异的地方：forall我会认为你输入的，都是一个集合里的东西，但是你这里的prop，代表的是一个集合吗？？？需要思考一下会不会导致严重问题
    mathematical_induction(p)

如果说引入新的keyword：
prop_prop mathematical_induction(p prop):
    p(0)
    forall n nat:
        p(n)
        then:
            p(n+1)
    then:
        forall n nat;
            p(n)

know forall_prop  p prop: 
    mathematical_induction(p)

// mathematical induction 也能被当做prop被传到prop prop里
prop_prop Q(p prop):
    //...

Q(mathematical_induction)

思考一下如果我不允许函数和prop的名字冲突，那我是否必要呢??

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
        p(x)
        t(x)
    then:
        q(x)
?
forall x A:
    dom:
        p(x)
    when:
        t(x)
    then:
        q(x)
dom 和 when 分离：一个专门表示定义域，一个表示在定义域基础上，还有额外要求
写在一起，在语义上，本质上是一样的，但是写一下貌似更分明？还是说确实有语义上的细微不同导致我必须分离他们？
这样一大好处是，可以引入iff
forall x A:
    dom:
        p(x)
    when:
        t(x)
    iff:
        q(x)
2. prop
prop x A:
    p(x)
    then:
        q(x)
vs
prop p(x A):
    p(x) // dom
    iff: // dom 上的额外要求. dom满足时 p(x)则q(x), t(x), q(x) && t(x) 则 p(x)
        q(x)
        t(x)
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
            cond(y)
            p(x)
            then:
                result(x,y)
        
        // (forall y: cond(y) => result(x,y)) => p(x)
        forall x B:
            forall y A:
                cond(y)
                then:
                    result(x,y)
            then:
                p(x)

    prove: // OK
        know p(1)
        forall y A:
            cond(y)
            then:
                result(1,y)

    when:
        forall y A:
            cond(y)
            then:
                result(1,y)
        then:
            p(1)    

4.11
2. add
   1. not
   2. or
   3. prop_prop
3. 例子
   1. 容斥原理
4.  

4.14
1. 可能要留个接口，让用户以另外的方式定义集合：直接把里面的东西写出来
   1. 现在 obj s set
   2. 之后可以让用户这样定义有限集合 obj s set: s = make_set(1,2,3)
2. 我严重怀疑when没有存在意义，用空的forall就能实现。未来让未来我不用对when操心，我应该把when删了
3. 我看了下，貌似让then里的forall，能有个一层，也是行的。不太困难

4.15
1. 要记住：
   1. 无休止地想集合论，在解释器层面把集合论相关的东西全部填满，是没意义的。litex要做的是，把 在“形式化” 集合论 的时候人们用到的潜意识，形式化出来。litex不需要内置集合论的所有性质。这些性质会以标准库形式出现，而不是内置在解释器里。
      1. litex的最底层不是集合论，而是比集合论还底层的东西：正则表达式匹配器
         1. 除了正则表达式匹配器，litex还提供基本关键词互相建立关系的能力。比如prove_contradiction和not。exist和forall。fn和exist unique
      2. 所以开发litex，读那些数理逻辑的书可能也没用：它们自称是数学的最底层，这我承认，但我比他们还要更底层一点
      3. 我觉得，人们在对集合论（最底层的数学）的性质进行推理的时候，仍然有很多事实进行了“默认”。（比如，=的意义，很多时候直接写上去了，也不知道为什么“两个一样的符号就能取等”。人们定义函数的时候，说是一定要先存在两个集合，才能定义函数。但union这个函数，它的定义域是集合的集合）这些被默认的知识，并没有被形式化，也没人去形式化。我相当于把这些潜意识做成了litex。
      4. 集合论里的性质和普通数学不一样的地方
         1. 值得一提的是，这些集合论的性质也是可以被形式化的。只要是可以被形式化的东西，就是lix代码，而不是内置在我解释器里的
         2. 集合论里，union, intersection 这样的函数，它们的定义域是集合的集合。也就是说，集合论里，函数的定义域是集合的集合。这在普通数学里是不允许的：为了防止罗素悖论，不能引入集合的集合
         3. prop是作用在某个集合上的。所有prop被放在一个集合里，应该是不允许的。所以prop之间的运算，很诡异，因为通常来说运算是要定义在集合上的，而prop之间的运算并没有定义在集合上。
2. 我需要内置的东西是，没法被litex语法形式化的，但人们默认是对的逻辑
   1. 三段论：是我送给用户的。不送给用户，用户不可能在litex里把三段论模拟出来
   2. 整数的加减法：自然数是我送给用户的。自然数的性质也是我的。因为正常来说，你一片代码里只能引入有些个符号，而我送给用户全体自然数这件事，相当于直接送给用户无数个变量了
   3. forall，exist，not，prove_contradiction 这些是我送给用户的。不送给用户not，不内置prove_contradiction的语义，用户不可能在litex里把not和prove_contradiction模拟出来
   4. 待办
      1. 建立exist和fn的关系：存在唯一能得到fn
      2. 快捷键：dom(f), 相当于取到f的定义域；取f的值域，用range(f)
      3. 引入有限集合{1,2,3}
         1. 描述集合有两种方式
         2. 取一个已经存在的集合，然后对里面的东西做要求
            1. 如果用户写了个 obj s set: p(s)，但是p压根不是作用在集合上的prop（比如p是作用在nat上的，但我却把它作用在了集合上），那这是用户的错误，和我无关
         3. 或者直接把集合的元素写出来：有限集合
            1. 有限集合有很多性质。比如用户问我这个有限集合里的所有东西是不是满足性质p，那有限集合就可以遍历整个集合来看是不是满足p，这对无穷集合是不可能的
      4. or
      5. 建立exist和forall的关系，这也需要内置
      6. impl & interface
   5. 我最大的问题是：不知道要内置哪些东西：哪些需要被内置？哪些不需要？我不知道。没有人和书和论文能参考。
3. exist 的工作模式，有点像去call一个事实来验证现在的事实
   1. 我可能会担心，如果不让用户去给事实取名，那我可能搜索空间太大了，不堪重负。为了防止这个。我还是允许用户给事实取名字（prop），如果我脑子很清楚，我就是去找某个prop来验证当前的事实，那我直接call那个事实的名字
   2. 这和exist x p(y) 很像：我知道x满足p(y)的各种性质
   3. 这里也和 集合+运算符 满足interface很像：我知道我要验证哪个事实，我拿现成的东西去凑
4. 当前目标：能实现95%的初等几何的命题就行。能在litex里模拟出来alpha geometry里出现的domain language
   1. 让语言完备化之后再说。先做一些阶段性的成果
   2. alpha geometry2 甚至还比1的语法多了很多条。本身ag1已经不是逻辑完备的语言了，然后还”有很多提升的空间让2来完成“，说明根本不需要特别的完备，也能实现了不起的事情。
      1. litex预计将在很长的时间内不能逻辑完备，甚至有很多bug。但这些问题都不是”第一性原理出了问题“
      2. 人们探索数学的时候，一开始也不会追求最性质广泛，最逻辑完备，也是从特殊到一般的。我也这么干。
         1. 等我有帮手了，再考虑怎么从特殊到广泛更容易。但现在我不考虑这些，我只考虑”让最该有的东西 先有着；不太重要的东西 之后再说“
         2. lean1 也没发布，lean1也是年薪百万的几个微软程序员做的。我再出发点高，我也不可能在细节的丰富度上打败这些微软程序员。我只能让我的第一性原理尽可能坚实，细节上打磨我完全忽略掉
5. 严格性vs自由度
   1. 还是保证自由度更重要：因为如果太严格，那证明一个什么东西都要“从头定义一大坨东西”，得不偿失
   2. 比如，*这个符号，作用在函数上，意思是
        fn *(f fn, g fn):
            forall x dom(f):
                x in dom(g)
                then:
                    (f*g)(x) = g(x)*f(x)
        其实这里是有问题的，比如：
        1. 万一f和g的值域压根不在一起呢，比如f值域是R，g值域是F2，那压根不能乘在一起
        2. 退一步说，不应该有函数的定义域是“所有函数的集合“这样的集合。而这里的*涉及到的就是所有函数的集合，非常错误其实
           1. 但如果你追求严格性，什么都写的很严格，那一方面，对用户要求太高，一方面确实浪费时间。那你写的不严格，反正我解释器验证的时候也不会帮你通过你写的不对的东西，那就OK了。
6. 上面的函数定义显然有很大问题：不能这么自由
先定义最原始的
fn *(f fn, g fn):
    dom(f) = dom(g)
    range(f) = range(g)
    then:
        forall x dom(f):
            (f*g)(x) = g(x)*f(x) // 解释器看一下g(x)是否真的能

如果f的定义域比g小，那让用户在小定义域上重新定义一个*，然后让这个小定义域上的结果等于大定义域上的函数，那就OK了

7. 唯一性貌似在lean里是内置的。这进一步说明litex也要内置一下这个。唯一性不是用户能自己用litex做出来的，是送给用户的。

8. 如果你要用到某个性质形如”存在xxx，则yyy“，那你最好用interface来表示这一类的东西，而不是用正常的东西表示
   1. 比如 可测集合上的可测函数。那你最好是 涉及到的可测集 impl 可测概念
   
比如可测函数的定义是：
设(x,f), (y,g) 是可测空间，f x -> y 可测，当 对任何s in g f^(-1)(s) in f
这就是按interface定义。而不是按”定义一些prop，让涉及到的东西满足这些prop“来定义


9. 先实现简单的，先实现特殊情况的。再考虑复杂的，考虑广泛情况的
   1.  从特殊到广泛，往往只需要添加一个涉及良好的，类似impl这样的关键词，就OK
   2.  现在看起来复杂的，无非是抽象层高，我基础设施不完备，所以看起来复杂。这是数学内蕴的复杂度高，不是我引入语法糖能解决的。所以一定要特别注意这一点，不要过早考虑复杂情况。过早考虑，会让我弄不清到底是我语言本身有缺陷，还是只是抽象层高带来的”看似litex不完备“。

10. 非常重要：如果一个运算符可以被用在很多的集合上，比如群定义中的*，它可能被作用在任何的 复合群定义的集合的 实例上，比如 求导符号 能作用在 任何 在某个区间上可导的函数 ，而这里的区间 可以是任何样子，所以 fn diff(f T) 这里的T是可以是 R->R, 可以是 R+ -> R+，总之就是T可以无限多。那这个时候，我怎么去定义这样的fn，这样的prop呢？用INTERFACE！！！

11. 如果把litex看做正则表达式处理器，那litex处理公式变换就相较其他语言有先天优势：如果不管语义，只是在看符号的重排和变换，那litex本质上就是做这个事情。
    1.  让我每天很难受的事情，其实是处理额外的语义：一个变量能不能作为合法的参数传入函数和prop这种，特别麻烦。
    2.  作为正则表达式模拟器，那litex现在就很厉害了
    
12. litex必须让then里能有forall，因为函数上的函数需要这个
新的类型写法：R => R 这种样子，不能单纯写成Fc了，要考虑可能是函数
fn exp(f R => R, n R):
    forall x R:
        exp(f, n)(x) = (f(x))^n
这里可以看到，必须要有then里能放forall，哪怕只是单层的forall
另外，为了方便，不妨让 形如 f()()这样的函数套函数的情况，一定能工作，如果是 g()()()这种，如果考虑起来麻烦，就先不考虑了.

14. litex 遇到的最大困难是，我需要自己定义任务
    1.  比如，有人会说，集合论是最底层的数学。这其实是有严重问题的认识。我至今没看到某本书里定义了什么是proposition。一个事实是对的，可能是被其他事实以什么样的方式推导出来的（用forall？用specific fact）。有哪些可以被判定的东西：1. specFact？ 2. forall fact？ 3.(not) forall fact 的 逆否命题 exist? 还有其他的吗？ 这些比 集合论还要更底层的东西从来没出现在教科书里，这很奇怪
        1.  如果这些“基本概念”被定义清楚了，那我litex直接就能实现好了。正是这些磨人两可，实则非常不磨人两可的东西，让我举步维艰总是要改这改那。

15. litex采用朴素集合论。这和类型论是不同的。类型论内蕴了对ZFC公理的非常严苛的检查。而litex甚至允许用户自己去定义公理（毕竟我只是一个正则表达式匹配器，任何匹配的规则，用户都能自定义），用户定义的公理，不论是 可能导出矛盾的（罗素悖论被发现前的集合论公理体系），还是不能的 （现在的ZFC），反正我就 送给了你最低级的约束（比如z in a 没证明，我不允许你 fn f(x a) 套用在 f(z) ），然后剩下的事情都是用户自己看着办。
    1.  不送给用户这样一套内置在语言里面的系统是有道理的。
        1.  这里有个抉择：用户能自己定义公理体系吗？还是我内置好了送给用户
            1.  我选择送给用户，这更符合前年来数学世界的发展规律。
            2.  即使我用了类型论，那未来再来个超级类型论，我还要改成基于超级类型论吗？我要做的是，让用户能在我的语言里形式化类型论，集合论，“超级类型论”，或者他们自创的什么理论，然后让他们自己基于这套体系做推理。如果确实出现自相矛盾的点，他们也应该用 not p(x) 是 true 然后 p(x) 也是true这样的方式去发现。我编译器不会因此报错。只不过用户会发现 not p(x) 和 p(x) 在用户自创的公理体系下，同时成立。这说明他的公理错了，而不是litex错了。litex不检查用户的know，即用户的公理我不检查。我只是拿你的公理往后推理。
        2.  最大的意义：类型论学习成本太高了。朴素集合论更有性价比

16. 我的形式化语言只是一个正则表达式处理器。我需要内蕴这些避免悖论的方式吗？比如用户know s set: s in s. 用户这么写，我应该是报错吗？但我觉得报错是不对的，因为用户用了 know ，这是他自己犯错了，和我无关。我不想就此设计保存机制，太麻烦了。而且用户定义各种各样的公理体系，我觉得都是合理的。哪怕用户自己定义的公理体系是有悖论的。我只要保证我按我的方式工作是对的。我也没错啊

检查的严格度：
1. Lean > Litex
2. Litex 没有内置公理，也没有内置对某些公认的”错误的“事实的检查。不管是公理，还是”错误的公理“，用户只要用know关键词，我都认为你是对的
   1. litex比所有公理还要底层。litex是个正则表达式匹配器。我不预设任何公理，我只预设了一个正则表达式匹配器、一些常用关键词、一些语法糖和语义糖（比如fn f(x A) 而不是 fn f(x)，因为这样的fn更像是数学里出现的fn：参数是来自一个集合的，而不是凭空而来的）
3. 严格度的解释：为什么我觉得litex这样的严格度够了
   1. 如果要像lean那么严格，即有些用户的know我也能检查出错误（比如简单版本的罗素悖论），那我必须要引入类型论，这样litex就失去优势了
      1. 99.9%的情况下，用户根本碰不到这么底层的逻辑，不能为了0.1%的情况牺牲整体的使用
      2. 如果用户专业到意识到了litex的缺陷，那我相信这点严格性的缺失也不会造成什么困难，用户的自律性可以让严格度不必那么高。就像C语言会内存泄露，但专业C程序员通常不会内存泄露。
   2. lean虽然更严格，但也没从根本上解决自指的问题。它只是让用户“没那么容易”自指，但用户稍微动下脑子，自指还是可以发生
   3. litex并没有默认任何错误的东西。它只是允许用户know错误的东西。这时候错误的责任是用户，不是litex
      1. 其实这也更符合litex的哲学。要知道人类在大部分时候发展数学，都是很不严格的。人们哪天发现了不严格，然后对不严格的数学修正。如果穿越到古代，那lean没人会用，因为强制要求所有人会了类型论才能做数学（这让大部分潜在用户望而却步），但litex任何人都能上手用。可见litex更符合人类历史发展规律，更符合直觉
   4. 我不内置任何公理。我对litex的定位是，比数学公理还要抽象度低一层。用户负责定义公理。用户可以蹭抽象层高的自然数出发直接开始；用户可以从抽象度低的朴素集合论开始；用户可以从抽象度更低的类型论开始。随便用户。用户也可以自己发明一套新体系
   5. lean内置了类型论，这很好。但如果我因为类型论好，我在语言层面上嵌入类型论，那万一哪天又来个”超级类型论“，我也要因为超级类型论更好而放弃类型论而用新的内置理论？
   6. 再退一步说，谁能说明朴素集合论，或者类型论里没漏洞？如果没法真的说明，那到底是朴素集合论好还是类型论好？这是说不清楚的。如果拿“类型论好，所以lean比litex好”做理由攻击litex，那本质上也站不住脚。
   7. 再再退一步说，让用户自己定义公理，相当于把“严格化”的权力和义务交给用户；把公理内置在litex里面（就像lean把类型论内置在语言本身里了），让开发者自己定义公理，相当于把“严格化”的权力和义务交给开发者。孰优孰劣，说不清楚的。
      1. 交给用户，那可以对用户就更flexible，用户自由度更高；交给开发者，那用户就更不容易犯错，但自由度低得多，学习和使用成本会指数上升。
         1. 用户可以自己在litex里轻松定义出朴素集合论，类型论，然后按他们喜欢的公理出发去做数学，不用只是按类型论的思维模式去工作。他们甚至可以发明一套新的公理体系。当然，他们自己定义的公理体系是不是自指的，是不是内蕴着矛盾的，我不帮他们检查。
      2. 另外，我是程序员，我不是数学家。我不懂这些什么集合论、类型论。所以我把形式化这些公理的权力和义务交给用户。我只提供我自己能理解的东西，即正则表达式匹配器。
4. litex 里的 fn 和 prop 和集合论里的有细微差别，只要不是最底层的集合论相关的数学，只要是基于集合论之上的数学，即函数的参数，prop的参数，必须来自某集合，那litex确实是满足的，即99.9%的情况都是和日常数学一样的。但如果参数列表里有参数的定义域是集合的集合了，如 fn f(s set)，那就有点tricky了，用户如果know了不该know的东西，那就回出错（如果不涉及这么底层的东西，比如 fn f(s nat)，即参数的定义域是一个给定的集合，那一切不会出问题（在朴素集合论的意义下不会出问题））。
   1. 这样的设计其实和lean也是很像的。lean的 fn 里面，传入的也不是普通的集合，而是所谓的type，type和set是不一样的。
      1. fn更像是C的struct，即“把一族符号放在一起”，而不是负责执行的东西。
   2. 虽然litex更flexible，看起来很容易犯错。但lean因为用的type，而type很难理解，所以反而会因为不直观而引入错误，甚至“写不出来”。
5. 注：需要特别注意的是，fn，prop，set这种关键词，在大部分场景下的情况下的行为和fn,prop, set这种事一样的，用户完全不用的担心。只有涉及到底层的东西时候，用户需要稍微小心一下会不会引入问题。
   1. lean的fn，prop也和日常的我们熟悉的fn和prop有点不同
6. 漏洞处理主要包括3个方面
   1. 避免漏洞
   2. 检查漏洞
   3. 纠正漏洞
   4. 在以上维度上比较litex和lean
      1. 在避免漏洞上，lean比litex更不容易写”语言检查不出来，但数学上自相矛盾的“的代码，之所以这样，因为lean写任何代码都很困难，要难20倍。同时，即使加了20倍的工作量，也不能避免漏洞
         1. 自指问题因为图灵停机问题，本质上是不能检查的
      2. 检查漏洞：如果写litex写出了”语言检查不到，但数学上自相矛盾“的代码，那通常用户是很容易一眼看出来”这行代码确实很危险“的，因为litex很简单，很直白；而lean虽然不容易写出”致命“代码，但一旦写出来，非常难以纠察出来。即lean不让你犯错，但一旦犯错就直接爆炸了
      3. 上面提到的都是语言层面上的查错。但语言还有社会上的因素。litex因为简单，所以用户多，就更有概率查出漏洞；lean因为难，所以对用户要求高，漏洞会因为语言用的人不多而一直不被发现。
         1. litex的哲学是：更方便地写代码，哪怕犯错了也更容易改，更多的人的加入能让语言发展更快，即使有些逻辑漏洞大家也能很快发现，很快找到；lean的哲学是：对用户提出博士生级别的要求，让用户很难写代码，以确保没有漏洞。
      4. 纠正漏洞：litex用interface来在抽象层之间跳跃，层级和层级很解耦。即使底层的一些漏洞被发现，只要这些涉及到的事实不直接影响上层，那剩下的所有代码都不会因此而崩溃，因为隔离隔离的好；而lean一旦发现问题，那就容易伤筋动骨全部都改
      5. 综上，litex在检查漏洞、纠正漏洞上有明显优势。在避免漏洞上，lean有语义上的优势，这让写有漏洞的代码很难，代价是写任何代码都很困难；避免漏洞上，litex有语法上的优势，因为语法清晰，可以一眼区分出哪些事实是没问题，的哪些可能有隐患
         1. 等项目较为成熟的时候，我做一个插件，让set出现在定义域的情况都warning一下。虽然我可以让你工作，但我也让你直观感受到可能出错的地方。
7. 人类在数学不严格的条件下发展数学这么多年，可见不严格也不是什么大问题；反而从前过于难懂的符号和表达方式，让大家对数学望而却步，让数学停滞。这就像litex因为不”过度的“严格，反而能发展。lean因为过于难懂，反而发展不快的。
8. 虽然不太严格，但本质上litex是要比lean表达更多种类的公理的。lean让你只能用类型论。litex里能很容易地形式化任何公理（朴素集合论，类型论）。
   1. 为了大部分用户使用方便，我用了set，fn，prop这样的关键词，但其实litex的这几个关键词不是单纯的人们熟悉的这几个词的意思。比如set可以是set of all sets。有些公理体系，这是可以的，比如类型论；有些这是不行的，比如朴素集合论。所以说，这些大家熟悉的关键词，虽然在绝大部分场景下，都是和大家熟悉的那个，意思一样，但本质上功能大得多。
      1. 我之所以不换个其他名字，还是沿用set，fn，是因为便于用户理解。
   2. litex不只是flexible，本质上功能要比lean大，因为我可以很容易的定义任何公理，而lean只能用类型论
      1. litex比最底层的数学公理，还要抽象层低，那就是：litex是正则表达式匹配器。
9. 证明litex完备性的另外一个办法：证明它能表示所有的proposition逻辑和一阶逻辑。
   1.  我设计整个litex的时候根本没学过这些”逻辑“相关的内容。我是为了验证完备性才去看一下的
10. 某种程度上，litex作为“新人”，就是要奇特一点，让“发烧友”先用起来，让他们爽。而我当前的正则表达式处理器，非常容易上手，非常有 设计理念的一致性，即你用litex学写一个定理了，你就立刻学会写所有定理了。这种”易学性“，来自于设计理念的”简单而功能强大“


语法糖

定义集合: 以定义正数集合为例
obj s set:
    s <= R
    # 下面相当于让s确实等于R+
    forall x s:
        x > 0
    forall x R:
        x > 0
        then:
            x in s

语法糖：更好的定义iff，相当于展开之后就是上面这个
set s = {x R| p(x)}
set s {1,2,3} 枚举
至于多个集合的叉乘，那就是interface了，不是正常的set了？
我暂时没想好，但用普通函数或许也？
fn *(A set, B set)set
fn index(s set, n nat) set
know forall A set, B set:
    index(*(A,B), 0) = A
    index(*(A,B), 1) = B
fn element_from_product_set(A set, B set, n nat) obj
know forall A set, B set:
    element_from_product_set(*(A,B), 0) in A
    element_from_product_set(*(A,B), 1) in B

只要不考虑集合论里的乱七八糟的东西，我就能很顺畅开展工作。只要考虑集合论里的东西（主要是集合论里 自由和严格 的边界太难把握了，我又不熟悉集合论。只有集合论是 “考验我语言是否准确”的数学分支，其他数学分支我都是直接实现就行）

要说严格不严格的话，为什么两个函数的叉乘里面的元素，都能形如 (x,y)? 这里括号()是啥意思？“取”出来是不是用了选择公理？这一些都是很tricky的。
我的litex，内部默认了一些朴素集合论公理是对的，但也有一些需要用户自己去定义。比如union，intersect这种，就让用户自己去定义里面的意思，甚至两个函数相等的定义是forall互相在in都能是用户自己轻易的。而set和in这样的关键词，是我送给用户的。存在一个集合叫整数集合，这也是我送给用户的。可以说，我自己也不知道我到底哪些公理我默认是对的。哪些公理我没默认，需要用户自定义，然后需要用户自查，我也不清楚。我只知道，用户对了，那就是对，即便用户基于的“对”的默认的事实是有问题的。我只是个正则表达式匹配器。

lean也不能完全避免错误其实
def RussellParadox : Prop := ¬RussellParadox  -- 定义一个命题，声称自身为假

theorem russell_false : RussellParadox ↔ ¬RussellParadox := by
  unfold RussellParadox  -- 展开定义
  simp  -- 直接得到 P ↔ ¬P

-- 导出矛盾
theorem false_from_russell : False :=
  iff_not_self RussellParadox ▸ russell_false

-- 可以推出任何命题
theorem one_plus_one_is_three : 1 + 1 = 3 := False.elim false_derived

这里用户也能定义出来 P <=> not P。然后用来证明任何事情

checkpoint: thoughts: why I should never go so fat in set theory and stick to the fact that litex is just a regular expression matcher. I by default in my language that some set theory facts are true and some are not valid, but not all of them are inherent in my language. User can still on his own define what set1 union set2 means, he can on his define what set1 = set2 means. I do not include anything with mathematical meanings in my language. I just compare symbols like a regular expression matcher. only very small amount of semantics is included: e.g. parameter in fn is checked , which is just syntax sugar (user do not need to write x in s, y in s as function requirement). Litex is a regular expression checker, but it is used in math, so giving users such syntax sugar is reasonable. if fn works like fn f(x,y), it is so flexible that it is hard for users to use. if fn works like fn f(x A, y B), where litex checks whether x is in x and y in is B automatically, is very useful for user, otherwise they just write fn f(x,y): x in A, y in B, and that is tedious. 

Fundamentally, 目前为止 that is still not function, because fn f(s set) is also valid, and no function can use set of sets as parameter domain.

还是说我内置一下整个朴素集合论，然后让fn里不能有set作为参数？用户只能以固定的几种方式定义集合？
比如我送给用户什么是union？
如何偷懒：我内置的stl里，我定义union，但我不允许用户输入

**答：我不内置任何公理。我对litex的定位是，比数学公理还要抽象度低一层。用户负责定义公理。用户可以蹭抽象层高的自然数出发直接开始；用户可以从抽象度低的朴素集合论开始；用户可以从抽象度更低的类型论开始。随便用户。用户也可以自己发明一套新体系**

我之所以不想内置朴素集合论，然后让用户不能自定义朴素集合论，是因为如果我确实想让用户定义有关集合的事实，那他们不可避免要用 prop P(s set), fn f(s set) 这样的东西，而这些都是不被允许的，如果我严格规定“集合的集合不被允许”的话。

**litex 和 lean的一大重要区别：litex允许你引入 {x| x not in x} 这样的集合，但之所以允许，是用户自己引入了它，是用户自己在 litex允许用户想做啥就做啥的时候 犯错了，这种场合litex没检查出你的错误，是吧允许的；但lean更严格，它不让用户这么写。**
**这样来看，lean似乎更加严格。但lean也因此引入了类型论，这加大了用户认知负担。**

为什么取dom这种功能或许是根本不必要的：这个时候用户在研究朴素集合论的函数这个概念。用户应该自己用litex来创造出函数这个概念，而不是直接拿来litex的fn（litex的fn和朴素集合论的fn不是一个fn；即使litex的fn能表达朴素集合论的fn，用户也应该自己像定义其他集合，其他东西那样，定义一个自己的self_fn，而不是拿我关键词研究）。直接拿litex的关键词研究，根本就是诡异的。你怎么能研究Keyword呢？就像你普通编程语言怎么去执行一个Keyword呢？我可以理解我的某些Keyword和用户平时用到的Keyword很类似，我也鼓励用户充分使用这里的相似，但如果你要研究它的话，请你先定义什么叫self_fn，而不是拿我的fn去研究。

4.17
1. AtomFact 还缺
   1. exist fact
   2. prop construct fact
   3. 得想一个更好的语法
      1. 可以是用 @ 给forall取名，这样forall 也能有not了
      2. 不一定和现有的specFact长得一样，但如果长的一样的话，那我就不用写新逻辑（match，parse）了
      3. 到底exist是和spec像，还是和forall语法像，是个严重问题。我之前觉得它和spec像，但从逻辑上讲，既然它是forall的逆，那应该和forall像？
      4. 给forall取名的另外一个好处是，证明的时候，不需要每次运行一遍forall，我可以看下这个forall涉及到的名字是不是已经被证明过了。如果已经证明过了，那就直接ok了，不用总是开个新环境运行了
2. or
   1. not和or应该和spec分离开来，而不是像现在这样耦合在一起
   2. 即有个placeholder，放or和not
   3. 本质上or不需要，因为not+and可以模拟出来or，但是or可以作为语法糖存在
3. iff
   1. 我要让forall的then里能放入forall，虽然放入的forall是单层的
   2. 当然，如果我给forall取名的话，我forall里的forall就可以不存在，即整个forall里只有specFact。但这很呆，因为我就是要让用户不需要给forall取名字。这样的话，很多情况下我都要给forall取名字

4.18
1. 整个litex最容易以不经意的方式引入编译器不报错，但数学上有漏洞的方式，就是引入不存在的集合。我只需要设计语法，确保用户以这样的方式引入集合，那一定不会出错，就ok了。即：有unsafe的引入方式，有safe的引入方式。
2. 需要用一种给exist，forall命名的方式，即还是要给事实取名（顺便也给specFact）取名。这比直接用prop p() 来代替一个 forall 看起来合理很多，虽然本质上它们是一样的
3. 要想想怎么call这些named fact
4. 还要想想如何实现 not，or，要在atomFact外面夹层
5. then里能forall
6. 一些 ”配件“
   1. 证明两个函数相等，相当于dom相等，在dom上的值处处相等（forall equal）
   2. 对函数，prop这种取dom
      1. 我可以让用户不能在fn的内部定义dom，我可以强制要求对dom的要求，全部体现在fn f(a s)的s里面
         1. 好处：
            1. 我写解释器容易得多
            2. 运行效率高很多：我检查你f(x)中x是否是f的定义域里的时候，我直接查一下x in s对不对，就行了，不用运行 fn f(a s): dom: cond(a) 中的 cond了。
            3. 更符合真正的集合论的写法，让用户用统一的写法：即所有的对定义域的要求，出现在集合里，而不是在fn或prop的局部里
               1. 如果代码短，这是坏事；代码长，这是超级好事
         2. 坏处：可能用户用起来不舒服
         3. 注：必须保留，因为要考虑到多个变量之间相互的关系，那只能局部引入了

4.19
1. prove:
    know:
        a  = 1
    a * 1 =1 # unknown
    a * 1 = 1 * 1
    a * 1 = 1
2. 貌似实现了exist和新版的not（or），我就实现一阶逻辑了
3. 另外需要考虑一下prop_prop咋弄
4. 虽然我从来没学过几阶几阶逻辑，但我在发明litex的语法（语义）时候，我发现我已经猜到一阶和二阶啥区别了：prop能不能作为参数传到prop里。
   1. 数学归纳法是最典型的prop_prop
   2. 可见litex实际上已经概念上很完备了
      1. 我本周因为生病了，所以睡不着；我思考我到底哪里不对：集合的集合不能表示，那union就不能定义，很难受，不知道问题出在哪了，不知道怎么对“严格”“不严格”做取舍。没想到是我在不知情的情况下碰到了一阶逻辑和二阶逻辑的界限。
      2. 我哪怕之前学过这些，可能也对我没帮助：1. 不知道这些怎么对应到我的语言里 2. 自己发现的，比学习来的，深刻10倍。
5. 注：垃圾回收器（比如CPython）确定一个内存可以释放的方式是，对一个obj进行reference count。如果count到0，那就释放（类似share_ptr的原理）；但是一个严重问题是，有时候，如果一个obj是互相引用的（比如class里的东西），这就没法用ref count了。所以每过一段时间，遍历一下所有的obj，看下”外部“对现在的存在的东西的引用是否归0。可见子引用是很本质的问题。litex处理iff的方式是，litex最多沿着树找2步，所以不可能循环走n步。

4.20
1. 给事实取名
@fact_name
< Fact > 比如fact可以是 specFact和ForallFact
2. 我发现#貌似是没必要的：我只要在离开当前环境向上查事实的时候，我如果发现我当前环境里声明了x，那我就不再往上找和x相关的事实了
3. exist
先只实现@fact_name forall 之后再想想这个语法还能用在其他什么地方

@fact_name forall/exist parameters # 单行的相当于只给现在这一个取名字
know fact_name
by fact_name, not exist fact_name
by not fact_name, exist fact_name

@exist_name exist/forall parameters
know exist_name
by exist exist_name, not exist_name
by not exist exist_name, exist_name
exist_name()

@fact_name: # 暂时不实现
    .... 很多事实。这里相当于给很多事实取名字。但这个时候不允许你not了。你可以用这一长串来by，推理出一个结论

by: 用多个事实证明then里的东西。这还是有搞头的。毕竟lean也是这么干的
    many facts
    then:
        ...

发现named forall 逻辑上等价于 prop p(). 确实是。但named的意义是，它立刻释放里面的东西，而不需要再让用户声明一下  forall ...
prop p():
    forall ...

exist_prop name(params) exist_params:
    ...
exist_prop name(params):
    ...
4. by
   1. by not exist_prop: 推出一个Forall
   2. by fact_name: 用指定的fact来检查当前的事实
   3. by fact_name_of_a_forall_fact: 推出 not exist
5. not 不应该绑定在SpecFact上，而应该是更高一层
6. set s = {x R| p(x)}
set s {1,2,3} 枚举
7. 因为正则表达式匹配太intuitive了。所以没有数学书说明：正则表达式匹配比数学还要抽象层低。其他很多学科也是这样的。
8. 现在大模型数学里有 1m 个定理
   1. 提高质量
   2. 字节也是左脚踩右脚自己生成代码的
9. lean 里完全没有图论(工作量更小，各个概念更加独立，甚至前沿图论也就4-5页，不用dependent在已知的事实，性价比总体上更高，想出来一个前人没做过的问题，方法用之前的人的用的就行)，分析（硬分析）也做不了，平面几何，

4.21
1. $必须要作为FuncFact的前缀，否则就会把 forall x A当做 relational fact
2. 为什么不能有 not forall 因为我不知道用哪个 exist 去 match 它
3. 因为 forall 不能有 not，所以只有specFact有not。这样我就能让not跟着specFact走；而exist被设计成和specFact走，所以我能有个field，同时包含not和exist的信息
4. 想到一个办法让not和exist都跟着specFact走，是很本质的发明。这个发明甚至说非常合理。完美地保持了litex设计观念的一致性：litex一切围绕在能match。为什么不能有 not forall 因为我不知道用哪个 exist 去 match 它。所以不能not forall。
5. 
# 这个表达式同时释放出 p 以及 exist_p。类似C++这定义class的时候，一些函数自动生成.
exist_prop a A, b B p(x X, y Y): # 可以没有 x X, y Y，用于 not forall
    dom(a,b,x,y)
    iff:
        IFF(a,b,x,y)

exist $p(x ,y) # 表示存在这样的a和b使得 dom(a,b,x,y) 并且 IFF(a,b,x,y)
exist_p $p(a,b,x,y) # 表示 a,b 就是是让 dom(a,b,x,y) 并且 IFF(a,b,x,y) 成立的a和b；如果这条成立，则立刻让exist $p(x,y)成立
not exist $p(x,y) # 表示 forall a A, b B, x X, y Y: dom(a,b,x,y) then: not IFF(a,b,x,y)
not $exist_p(a,b,x,y) # dom(a,b,x,y) 并且 not IFF(a,b,x,y)

4.22
1. # 这个表达式同时释放出 p 以及 exist_p。类似C++这定义class的时候，一些函数自动生成.
exist_prop a A, b B p(x X, y Y): # 可以没有 x X, y Y，用于 not forall
    dom(a,b,x,y)
    iff:
        IFF(a,b,x,y)

exist $p(x ,y) # 表示存在这样的a和b使得 dom(a,b,x,y) 并且 IFF(a,b,x,y)
have a,b $p(x,y) # 表示 a,b 就是是让 dom(a,b,x,y) 并且 IFF(a,b,x,y) 成立的a和b；如果这条成立，则立刻让exist $p(x,y)成立
not exist $p(x,y) # 表示 forall a A, b B, x X, y Y: dom(a,b,x,y) then: not IFF(a,b,x,y)
not have a,b $p(x,y) # dom(a,b,x,y) 并且 not IFF(a,b,x,y)

2. 数列收敛的定义
forall a sequence, e > 0, exist N, forall n, m > N, |at(a, n) - at(a, m)| < e

exist_prop (N nat) Cauchy(seq sequence, epsilon real):
    epsilon > 0
    iff:
        forall n nat, m nat:
            n > N
            m > N
            then:
                |at(seq, n) - at(seq, m)| < epsilon

know:
    forall epsilon real:
        epsilon > 0
        then:
            have epsilon*2 $Cauchy(seq, epsilon)

forall epsilon real:
    epsilon > 0
    then:
        have epsilon*2 $Cauchy(seq, epsilon)
        exist $Cauchy(seq, epsilon)

3. 基本观念：正如两个在py里的一样的函数，只要不同名，那 func1 == func2 不成立。在litex里，两个形式上一样的forall 也是不能比较的。这导致 注定有一个瞬间，需要用户像使用 exist 那样，给一个forall取名，才能让我的matcher能继续工作.在exist这个地方，让用户引入“给forall取名”这个观念，是合理的，不只是让我实现解释器容易，也是让用户思考起来更容易：用户知道什么时候取名，以及怎么取名，以及怎么用取了名字的forall。

4.26
1. 字面量不只是自然数难处理，{1,2,3}这种也是字面量，理论上最好也能“在该出现的地方出现，能方便用户使用”
2. set 本质上 和 = 一样，是和其他东西不一样的东西。应该给他们单独开出来一些 litex 的语义（或者说litex的内部变量），来专门处理
    1. 特别是某个set = {1,2,3} 这种
        1. 这里有些继承关系，比如 a subsetof b, 但 b = {1,2,3}，那a    
    2. forall x S，如果S是{1,2,3}这种，那有另外的证明uniFact的方式：遍历整个集合
        1. 但因为litex还没智能到判断如果 a < b 而 b = {1,2,3}，那a < {1,2,3}，所以如果用户需要遍历a来证明一个事情的时候，我不帮你遍历
3. claim 需要改一下语义
    1. 因为claim 的语义是，我claim一个事实，然后我需要用这个事实推出一个结论。
    2. 但最好是，claim 真的开了个环境，整个环境里能定义各种变量之类的，而不是很孤立的，只是开了个新环境来证明，应该是开一个新环境里先放入forall里面的参数，然后进而证明
        1. claim也有两种：一个是以 : 结尾的那种；一个是 claim forall 这样些的；后者会开局部环境并导入变量，前者只是开了个独立环境，哪怕是 claim: forall x x: ... prove: 这种，x也不能出现在prove下面
4. impl 也是一种 事实，而不是一个 type def 的一部分
    1. 考虑下面情况：forall f fn => fn, g fn => fn:  {Int, f, g} impl Group
        这是可能出现的：对于任何取余数的加法运算，在Int上面，都是Group
    2. 为了让这种 impl 事实 能被 forall export，那我就得让 impl 也做成一种 事实，而不是一个 type def 的一部分
5. 我的 or, and 类型的事实，不包含 forall，否则整个项目太乱了
    (not) specFact (pure, exist, impl) => or/and => unifact
    如果 or下面也能有 forall，那上面这个链条就出问题了。我要存储 unifact 下面的 specFact的时候，我的存储方式也是 uniFact propName 做key，存 specFact 所在的 一层层的 or/and， 最后放在某 uniFact 下面
    另外，or 和 and 在证明的时候需要 取 not，那取 not 只能是 SpecFact了
6. 存 forall 套 forall
    know forall x A:
        dom:
            $cond(x)
        then:
            forall y B:
                dom:
                    $cond2(x, y)
                then:
                    or:
                        $p(x,y)
                        $t(x,y)
                iff:
                    $pp(x,y)
        iff:
            forall y B:
                $q(x,y)
    存储：
    1. $p(~x, ~y) under or($p(x,y), $t(x,y)) under forall x A, y B: $cond(x), $cond2(x,y), iff: $pp(x,y)
    2. $pp(~x, ~y) under forall x A, y B: $cond(x), $cond2(x,y), iff: or: $p(x,y), $t(x,y)

    证明 forall + iff 的方式和普通的 forall 也不一样，要把 dom 和 iff 混起来做 条件

4.30
1. 特殊形式的 Fc
fn(a A, b B) => Fc
如果你要对a和b同时取要求,比如a A1, b B1: forall a A1: $p(a,b)，那就请自定义一个B，让这个B = {x B| forall a A1: $p(a,b)}，然后你就可以对a取要求a A1，对b取要求b B了。此时，fn(a A, b B: $p(a,b)) => Fc 就变成了 fn(a A, b B1) => Fc。

2. 另外一个定义set的方式：是一个函数集

3. 要测试什么东西
    1. 基础设施
    	2. forall 套 forall

4. 之所以要在 forall, prop, fn 里放入dom，是因为，我会把它们看成一个接口。如果是为了这样一个接口，而让用户要定义一个set，让这个set是 interface 的要求（dom），我觉得不合适。
	1. 但有时候我涉及到的变量的集合，是要写非fc的，比如要传入一个函数，这个函数的dom是xxx，而描述dom的方式是需要用 specFact的，这时候就不能使用常规的fc了
	2. 方法2: 我传的时候，只是传fn这种，然后在 dom 里详细描述。如果用户没有描述清楚，那就报错
    3. 方法3：我让用户用 inline 的 forall 这种写法来给 fn里面的参数提出要求，但是我实际存的方式是，我只是把fn存成 setfc，然后把对这个 fn的要求，存在dom里面，这样我不需要修改 runtime，我只要parse得好就行


5.1
1. 虽然inheritance 有种种缺陷，但它有一个核心好处：让符号重载变得可能，既子类能自动获得母类的符号重载
2. litex 里也必须要实现函数符号重载，引入新的关键词 extend
know:
    nat extend int: # 基本意义：nat >= int。这是需要验证的。extend是一种特殊的fact。
        __nat__add__ extend __int__add__  # 这里放入同名的函数（opt）. 这里的意思是 __int__add__ 有的性质，__nat__add__ 保持。
        __nat__sub__ extend __int__sub__
        __nat__mul__ extend __int__mul__
        __nat__div__ extend __int__div__
        __nat__pow__ extend __int__pow__
        __nat__eq__ extend __int__eq__
        __nat__ne__ extend __int__ne__
之后如果遇到了 a * b， a 是 nat，b是 int，那就调用nat的__mul__，因为我要找 extention 等级最高的那个。如果全是 int，那我不会去找 nat 的__mul__ 。 因为 nat 的 __mul__ 的性质，int 都有。
3. 把 extend 做成 事实是有很多好处的，就类似把 impl 做成 事实一样。
    因为逻辑上，这确实是一种 ”判断“
    如果你想让这种 “判断” 被默认成立，用 know 就行
    impl, extend 这种，是有额外功能的fact，它们相当于语法糖
    当然，现在我不确定impl是否有意义，因为我直接一个个传东西应该也行
    prop AbelianGroup(G set, id G, mul fn(G, G) G, inv fn(G) G):
        $Group(G, id, mul, inv)
        iff:
            forall a, b, c G:
                a \mul b = b \mul a
4. impl 的这种写法，相当于把 集合+元素+运算符 放在一个 struct里面，放在一起传递；类似于C的struct的效果；而因为我现在语言我不想再添加新的语法，所以我让它们裸奔地出现在参数列表里。
或者可以加个语法糖
structure Group(G set, id G, mul fn(G, G) G, inv fn(G) G):
    $IsGroup(G, id, mul, inv)

prop IsGroup(G set, id G, mul fn(G, G) G, inv fn(G) G):
    iff:
        forall a, b, c G:
            mul(a, mul(b, c)) = mul(mul(a, b), c)
        
        forall a G:
            mul(id, a) = a
            mul(a, id) = a

        forall a G:
            mul(a, inv(a)) = id
            mul(inv(a), a) = id

prop AbelianGroup(@Group(G, id, mul, inv)): # G, id, mul 必须出现，因为iff里面要用
    iff:
        forall a, b, c G:
            a \mul b = b \mul a
这里@会自动展开成 G set, id G, mul fn(G, G) G: $IsGroup(G, id, mul, inv)

call 时，用 AbelianGroup(G, id, mul, inv)  就行

相当于用户这么写，然后我编译的时候就把它展开了。

类比C：C中struct其实也是一个”占位“的东西，在编译的时候会被展开。所以你可以看到 用户可以在 应该写 type 的 地方原地定义一个 struct {} 。这本质上就是 原地编译那个 所谓的 struct。这和我的 @ 的设计师一样的。

这里相当于能在 参数列表里写 specFact + param + set ，能引入 临时变量的感觉

5.2
1. 如果 forall 里 出现 prop 也是 传入的，那必须要另加考虑，和现有的整个体系独立开了
不能让它进入 forall，因为我当前的match方式(通过match 存储的同名事实)，根本不支持 prop 也是自由的。
如果你要call 这个 事实，那你只能 直接call prop名
我允许你 在 forall的 参数里 传入 prop，但不允许你 在 forall 的里面的什么地方让某个prop 名是 这个 传入 prop名。
prop p(q prop, t T):
    $q(t)
$p(t)

prove:
    structure Group(G set, id G, mul fn(G, G) G, inv fn(G) G):
        dom:
            # ...
        iff:
            IsGroup(G, id, mul, inv)

    prop IsGroup(G set, id G, mul fn(G, G) G, inv fn(G) G):
            forall x, y, z in G:
                mul(x, mul(y, z)) = mul(mul(x, y), z)
            forall x in G:
                mul(x, id) = x
            forall x in G:
                mul(x, inv(x)) = id
            forall x in G:
                mul(inv(x), x) = id
            forall x in G:
                mul(x, inv(x)) = id

    # 因为通常 G, id, mul, inv 不会同时出现在specfact里，所以普通的 match 的方式是不工作的；那为了让 G, id, mul, inv 同时能被解释器知道是哪个，需要额外的方式。比如像这里用特殊的forall，这种forall专门match claim <>

    know forall <Group(G, id, mul, inv)>, x G, y G: 
            mul(x, y) = mul(y, x)

    claim forall <Group(G, id, mul, inv)> x G, y G:
        mul(x, y) = mul(y, x)

    forall <Group(G, id, mul, inv)> x G, y G:
        mul(x, y) = mul(y, x)

如何call一个带<>的forall或者prop？

<Group(R, 0, +, -)>:
    # 后续的证明。后续的证明时，我会参考所有的涉及到 <Group> 的事实，把 <Group> 展开成 R set, 0 R, + fn(R, R) R, - fn(R) R

本质上litex的大部分语义上的设计，是为了能 match 上 known 和 given

extend 起到了 ”继承“ 的作用，但总是提供单层的 继承，不会有 多层的继承，这让它很好

forall p prop 也能用 这样的 <> 表示了

structure Mathematical_Induction(P prop(n nat)):
    iff:
        $P(0)
        forall n nat:
            $P(n)
            then:
                $P(n+1)

# 之后再这个环境下面的所有的东西，都会调用一下 包含 <Mathematical_Induction()> 相关的事实

forll < Mathematical_Induction(P) >: # 打开这个环境,就让P绑定 structure里的条件，相当于 forall p prop 了
    forall n nat:
        $P(n)
    
验证、存储、调用 forall p prop, 甚至 forall p prop: forall q prop 这种，还是用 prop 来吧。你真的想验证并释放，必须用 $math_induction(q) 这种。不要尝试用其他的 

prop everything_true_prop(p prop(x X)): # 这个没法以 forall 的形式在环境里释放，因为 p 是不固定的；用户要验证，只能我引用额外的验证方式，来原地验证. 这里的 X 必须是已经定义过了的。如果你想让 X 没被定义过，那就 prop_prop everything_true_prop(X set,p prop(x X)): 这种，X 是自由的
    forall x X:
        $p(x)

know $everything_true_prop(p) # 释放 forall x X: $p(x)

know:
    forall p prop:
        $everything_true_prop(p)

$everything_true_prop(p) # 用prop的定义来验证

know:
    forall p prop(x X):
        dom:
            $cond(p)
        then:
            $everything_true_prop(p)

    know $cond(q)

$everything_true_prop(q)

注：还是不要让 prop 出现在 structure 里，因为我要让 prop prop 只能出现在 prop里，用特殊的匹配方式去匹配

5.3
1. 如果处理 集合互相相等的问题
    这个问题很重要，因为我把变量代入一个fn，prop的时候，我需要检查它是否在集合里。而如果我代入的是 fn，比如 prop q(f fn(x X) Y)，这样我传入 q(g) 我需要检查g是否是 fn(x X) Y. 但比方说我定义的时候，我是 fn g(x X2) Y2，那我需要检查 X2 和 X 是否相等，Y2 和 Y 是否相等。我不只需要有个内置判据来证明集合相当，还要有判据证明两个 fn 相等

<Name(x, y)>:
    ...

2. 把extend做成fact的好处是，我可以 forall ... extend ... 。这样能做到 forall 的能力
3. structure 也可以做成prop（本质上它就是一个prop），然后任何prop都能出现在 <> 里。它出现的意义无非是 能让我解释器match上

REMARK: 我认为类似 ipynb 那样，做lixnb 也是合理的，因为litex是数学语言，可能会有很多伴随的注释。如何让注释和代码混在一起，是值得思考的。

5.7
specific fact => logical expression => universal facct
sun is red => or: sun is yellow, sun is red => forall x X: or: x is yellow, x is red
为了让我能match，人为规定，or下面只能有specfact，不能有forall
因为我必须要让or里面的东西能not:否则很多东西证明不了了
比如
know or:
    x = 1
    x = 2
know not x = 1
x = 2 # true

因为 not forall 我是没法验证的，因为我不知道从哪里找一个obj来，说明 exist obj such that forall 下面的事实都是错的

not forall x ; $p(x) 不能被保存，也不能被验证: 如果要证明 not forall 则相当于找到下面
exist x not $p(x)
但因为我是正则表达式匹配器，我不能帮你找到它

exist_prop x X st exist_not_p():
    not $p(x)

or:
    exist $exist_not_p() # 相当于not forall 被写成一个 specific了

怎么证明 exist_not_p() 呢？

know: not $p(1)

exist 1 st $exist_not_p() # 1. 它自己成立了 2. exist $exist_not_p() 成立了

这里为什么要有空括号呢，这里的括号是要传参的

exist_prop x nat st $exist_nat_smaller_than(y int):
    x < y

exist 10 st $exist_nat_smaller_than(100)
exist 0 st $exist_nat_smaller_than(-1) # unknown

整个系统的设计是为了 1. 正则表达式能匹配上 2. 用户用起来直观

我有6种specific fact
1. true atom
2. false atom
3. true exist
4. false exist
5. true exist  st
6. false exist  st

这6个为什么是平级的

spec => logic => universal
为什么我把这6种情况设计成
atom => true/false atom => true exist/ false exist => true exist st/ false exist st => universal
或者进一步拆分，或者 更直白的，为啥我要有这个关系，我 exist st 和 普通 exist 和 普通 spec atom 完完全全独立开来工作行吗？
即我有6个数据结构，而不是写在一个 SpecFact 里 仅仅是 enum 表示不一样，而 data structure 是一样的

本质上
1. 我一个人开发没力气
2. 他们都是正则表达式匹配的正则表达式，对我而言没区别。它在数学上啥意思，和我关系不大，我只要能匹配就行。匹配的规则都是统一的，所以没关系。

另外不要小看有st和没有st的exist的事实的设计，非常巧妙；没有st的时候，就不需要每次放两个无意义的占位符在那里了。

prove:
    know:
        forall x nat:
            or:
                $p(x)
                $q(x)
    

        forall x nat:
            dom:
                forall y nat:
                    $q(x, y)
            $p(x)
    
        和 下面这个逻辑上一样，但语义不一样

        下面这么写的话，这个forall是不会帮到我验证的，因为我找不到y
        forall x nat, y nat:
            dom:
                $q(x, y)
            then:
                $p(x)    
        
        当然我不能让你 forall 套超过2层，因为我搜索的时候是 n^2 量级，3层就是 n^3 了

        golang 的 内部的 interface 从来没超过一层，我的语言也是

prove:
    forall x nat:
        $p(x)

    forall x nat:
        x > 0
        then:
            $p(x)

    forall x nat:
        dom:
            x > 0
        then:
            $p(x)
        
    # universal fact的iff 是2组forall-then的语法糖
    forall x nat:
        dom:
            x > 0
        then:
            $p(x)
        iff:
            $q(x)
        
    
    forall x nat:
        dom:
            x > 0
            $q(x)
        then:
            $p(x)

    forall x nat:
        dom:
            x > 0
            $p(x)
        iff:
            $q(x)

    # prop 的定义也有iff，它也是语法糖  
    prop p(x nat):
        dom:
            x > 0
        iff:
            $q(x)
        
    prop p2(x nat):
        dom:
            x > 0

    know:
        forall x nat:
            x > 0 # 可能要写在 $p2前面，因为要满足p2的定义域
            $p2(x)
            then:
                $q(x)

        forall x nat:
            x > 0
            $q(x)
            then:
                $p2(x)

电脑一开始是被用来做数学证明的

Recursive Functions of Symbolic Expressions
and Their Computation by Machine, Part I

A programming system called LISP (for LISt Processor) has been developed
for the IBM 704 computer by the Artificial Intelligence group at M.I.T. The
system was designed to facilitate experiments with a proposed system called
the Advice Taker, whereby a machine could be instructed to handle declarative
as well as imperative sentences and could exhibit “common sense” in carrying
out its instructions. The original proposal [1] for the Advice Taker was made
in November 1958. The main requirement was a programming system for
manipulating expressions representing formalized declarative and imperative
sentences so that the Advice Taker system could make deductions.

5.8
重要：equal => specFact => logic (or,and) => universal
equal 是特殊的spec，但它层级还要更低，因为我在match的时候，我看到了 $p(x,y)，我就会找 所有形如 $p(x1,x2) 的specFact，然后验证x ?= x1, y ?= x2，即每次验证（match）spec fact 的时候，我都会调用 equal fact，这说明equal是更底层的。

如果一个logical operator 既有transitivity，又有commutativity，那就可以存成 rb tree，因为可以优化验证速度。最典型的是 = 。而且 = 因为它甚至比 spec Fact 还要底层，所以非常适合 拿出来，放在 特殊的数据结构里

暂时不清楚如何定义 set of fn with given requirements like {f fn(X)=>Y| f 的 要求}. 等我真的遇到要定义set of fn的时候，再考虑。
另外证明两个 set 一样，是个问题
如果我不允许用户在 {x | y}的y里面有forall型事实，而是只能放 spec fact 那就可以直接写了.

set: 能放任何东西；用in来做连接
fn_set: 只能放fn。能放在 set 出现的地方，表示fn的集合。
fn_set A fn(X) Y:
    # : 下面 放对集合的额外要求，相当于 {x T| cond} 的 cond
    forall y fn A: # 未来fn后面如果没写 fn(x)y ，即第一位不是(，那就认为你fn A后面这个A是fn_set 

fn f A 相当于 直接声明了一个fn叫A，这个 f 的定义域是 X, 值域是 Y (f 无额外的要求；如果你真的想要有额外的要求，那就写在集合X里，不要单独拿出来。事实上我对 fn 的声明里有 dom 这一项，有观望意见；它至多只是一种糖，而不是本质的，因为一般集合论的书写就是不会吧dom额外写出来的； 发现fn的dom是必要，如果 fn_set 这个关键词不存在的话，那如果在定义 fn 的时候，parameter list 里有 fn， 如果此时要对 fn 有要求，那需要借助 dom): 同时它满足 dom. 有点像

set A:
    cond

obj x A  # 立刻获得 A 的 cond 的所有性质. TODO: 不确定是否要用户一旦声明了之后，A下面的事实直接 以 specfact的格式 emit 出来


在实现 fn_set 前，要让 fn(x)y 能作为 fc 出现在集合的位置上; 然后要能自动验证两个 set 是相等的，相当于 两个集合互为母集

考虑 fn 的 type 怎么来写，即如何约定 fn 的 定义域，值域,估计是要放在 dom: 下面的，取 fn_dom(f), fn_image(f); 这里也能看出来临时的 dom 是很烦人的；如果不考虑临时的dom，只考虑 paramSets ，那就能 按符号来比较 fn 出现的 paramSet 的形状，而不是开个小环境来比较 


关于释放：
forall prop 也能 match: 需要有个新的 memory 能存 这种free prop fact       prove:     know forall p prop, x nat:         $p(x)      $q(1): free prop 是严重违背 litex是正则表达式匹配器这个特点的，不允许这种东西；你真的想释放可，定义的时候可以释放，不要想着用 forall p prop 这种奇怪方法

prop_set 是不必要的
我引入 prop prop 来和 普通的 prop 不一样。 prop prop 的定义域里可以出现下面这种形状
prop prop p(q prop(X)) 即里面能有 prop
prop_set 相当于 {q prop(X)| condition_on_q} 但这是有问题的： condition_on_q 会引入 “对于任意prop” 这样的语义。这是不被允许的： 1. 一阶逻辑不允许这么干 2. 我的匹配器不允许"forall prop" 这种东西。
prop prop 下面你也不能对q有任何要求，只能q作为 “作用在其他东西上的要求”
即：
prop prop p(q prop(nat)):
    dom:
        forall x nat:
            $q(x) # 这可以，因为q作用到其他东西上面

??
prop prop prop p(q prop prop(nat): dom...) 貌似也行。把 prop prop(nat): dom... 做成一个 prop_prop_set 也行。不过以后再说

下面这个貌似也能做成 prop_set
prop p(q prop(nat)):
    dom:
        forall x nat:
            $q(x) 

prop_set S prop(nat):
    forall q S:
        forall x nat:
            $q(x)

prop prop p(p S)

这么干貌似也行，不过这里不应该是 forall q S (forall 里不应有prop作为参数)，而是另外找一个keyword来表达同样的意思

先是能一阶逻辑得了，以后再考虑二阶。高阶本质上就是叠加prop：prop prop; prop_prop_set。
高阶的逻辑会给我带来的困扰是，forall 里 会出现prop。虽然，我可以引入新的 keyword 比如叫 prop_for_all 来区分普通的 forall 和 这里的可能出现 prop 作为参数的forall，但这太烦人了。我先把主要功能实现了再说

本质上 ”升阶“ 的过程，就是往 prop 的参数列表里放 prop 的过程。如果 prop3 的参数列表的 prop2, prop2 本身是 prop prop (prop prop 相当于读入prop的prop), 那 prop3 就是3阶的，prop2是二阶的。

本质上必须要有 prop prop 是为了让数学归纳法成立。我实际上留个结构让 数学归纳法作为内置的东西成立，也行。

REMARK:
注：为了不要考虑prop prop; prop_set 这样的东西，我直接内置把数学归纳法送给用户；我不考虑命题逻辑，和除了数归法以外的其他高阶逻辑。

除去掉数学归纳法，是不是朴素集合论不需要引入 能读入 prop 作为参数的 prop 了？
在朴素集合论中，命题（proposition）的处理通常不涉及高阶构造，即不需要将命题本身作为其他命题的参数。具体来说：

朴素集合论的基础
朴素集合论主要基于一阶逻辑，其中：

集合通过外延公理（成员关系）定义。

命题（如 x∈A）是逻辑语言中的基本表达式，但集合论本身不将命题视为集合的成员或参数。

数学归纳法与命题参数
数学归纳法（在皮亚诺算术或类似系统中）需要将命题 P(n) 作为参数，形式上涉及 命题作为变量（即一阶逻辑中的谓词变量）。这属于 一阶逻辑的语法能力，而非集合论的公理。朴素集合论本身不直接处理这种命题参数化。

是否需要高阶构造？

若仅讨论朴素集合论（如策梅洛-弗兰克尔 ZF 的无形式化版本），其公理（如配对、并集、幂集等）仅操作集合，不涉及命题的高阶处理。

若将命题视为集合（如在某些形式化中通过编码），则需引入 命题集合，但这已超出朴素集合论的范畴，属于形式化元数学或高阶逻辑。

替代方案
即使不用数学归纳法，朴素集合论中定义递归或归纳结构（如自然数）时，可能需要某种形式的归纳原则。但这类原则可通过集合存在性公理（如无穷公理）实现，而无需显式将命题作为参数。

结论：朴素集合论本身不依赖“以命题为参数”的机制，数学归纳法的需求源于对归纳结构的定义（如自然数），而非集合论基础。若仅讨论集合的构造与操作，命题参数化并非必要。但在形式化数学中，若需将证明或命题本身对象化，则需引入更高阶的系统（如类型论或二阶逻辑）。

5.9
1. 既然我已经选择了 用类似 C 的类型系统(litex 里叫 集合系统，因为数学里没有类型只有集合。不过因为同一个元素可以出现在很多不同的集合里，所以和C的类型系统也没那么一样：C里面一个元素只能在一个类型里。不过这貌似没啥问题，因为涉及到的prop和fn会规定它在哪个集合里，我就知道涉及某个函数或者prop的时候传入的参数是以哪个集合里的元素出现在里面的)：
    类似C的类型系统：无oop，无类型继承，甚至没有类型组合（没类go的interface系统）。存在符号重载，不过是只有 数字字面量的加减乘除可能有重载（此时要确定它是哪个类型，用后缀来区分）。因为没OOP系统，所以不能实现 函数重载。
    我现在遇到的难题是，如果表达函数的类型。那我也应该类比C的函数的类型的写法。1. 正常传 函数指针 2. 用 类似 fn_set 的表达 函数集合。这会在have里用到。
    
2. 就像任何语言一样，在引入新类型时，是是 形如 fcAtom 这样的；但涉及到 函数的时候，就变成 复合形态的 类型了，就要用 fcFn 来表示了。

5.11
参数的类型确定，那我能重载函数名。函数名不能重载，那我就能重载变量类型。

图灵机 ＝ 可以把0变1 1变0的纸带 加 判别器 加 指针。指针在纸带上 跳动，让图灵机完备了。但判别器本质上只要做比较(机械地做模式匹配，这里的模式可以是不内蕴递归的，所以不需要用循环;如果模式被允许内蕴递归，那就用另一个图灵机来做判断器。新的图灵机用的判别器，又是可能内蕴递归的，那就在分类讨论。总有一个时刻需要不是图灵机判断图灵机，这时候就是 不含循环的判别器来判别了。）就行，不需要做循环，所以可以不图灵完备。这就像通用编程语言和litex的区别:一个图灵完备(事实上大部分编程语言的实现都是内部实现了一个虚拟机，虚拟机就是一个图灵机) 一个不需要完备。

5.12
package managment system: 不能有包里套包。如果包a需要引用包b，包b引用包c，那需要让包显式地引用包c；即如果说整个包在一个folder里面，而folder下面有一个folder里全是reference pkg，那本质上这个 reference pkg 里的folder都和 当前这个包的folder的其他文件是平级的。这样用户调用其他包里的东西就更容易，同时我 xxx::yyy就够了，不需要xxx:yyy:zzz。
litex是一个超级fancy的read-only turing machine。这里严重问题是， Read-only turing machine 是 context-free 的不能有*。那我必须要能“数数”，以让 x + x = 2 * x 成立（单纯的context-free的图灵机不能数数，所以需要一个context-sensitive的图灵机来数数）。那我就要人工引入 $is_string(setName) 来 判断是不是一个东西是环；如果是环，那我可以帮你计算 2 * x = x + x （验证方式：帮你按字典序排列，然后按string比较）
字典序排列这个还是很本质的：可以考虑只要是实数（复数）加减乘除 如果涉及到纯 数字，那就直接计算出来，而不要一直是 2 + 2 这种形式到处乱飞，让它以4出现。某种程度上这就解决了“数数”的问题.

% 我还没引入

我意识到 x + x = 2 * x 貌似还没建立联系: 或许我在做任何有关 实数或者说复数的加减法的时候，我要人为地 重排一下，然后按 字典序去排列一下. 这样的另外一大好处是，我 存事实的时候，我直接存化简了的东西，而不是 保存 $p(2+2*1) 然后每次都运算一下 $p(4) 和 $p(2+2*1) 的比较
另外一个是 x * x = x^2 
数数：主要是枚举：现在没法证明，未来可能也没法证明，forall x in nat: x < 10 then or: x = 0, x = 1, x =2 , … x =9，因为不能从 < 10 推理出来是 0 到 9，除非我 引入新语法
可见 涉及到数数的事实，很多，很杂，我不知道怎么处理完备。也许引入一个新语义一下全部解决了，也可能一直没法一下解决，就和现在的只读图灵机打架，因为只读图灵机不改变新信息，而数数是需要不断改变counter的信息的

可能这要的递归法可以写成
know forall x nat, n nat:
    y < n + 1
    iff:
        or:
            y = n
            y < n

know forall x nat:
    x < 1
    iff:
        x = 0

know forall x nat, n nat:
    x < n + 1
    not x < n
    then:
        x = n

know forall x nat:
    not x = 0
    then:
        x > 0

此时
claim:
    forall x nat:
        x < 2
        then:
            or:
                x = 0
                x = 1
    prove:
        forall x nat: // true
            x < 1 + 1
            iff:
                or:
                    x = 1
                    x < 1

        # fact1
        forall x nat: // true
            x < 1 + 1
            not x = 1
            then:
                x < 1 
                x = 0

        # fact2
        forall x nat:
            x < 2
            not x = 0 
            then:
                x > 0
                x = 1

        forall x nat:
            x < 2
            then:
                or:
                    x = 0 # 它不对时，fact2 成立
                    x = 1 # 它不对时，fact1 成立 

5.13
prove:
    know:
        or:
            or:
                $p(x)
                $q(x)
            $t(x)
    
    or:
        or:
            $p(x)
            $q(x)
        $t(x)
不知为啥不工作
能工作了

注：如果我要函数名重载，那变量的类型（集合）就不能重载；如果我要变量所在的集合重载，那我函数名就不能重载

注：现在每个文件运行好，然后打开新项目的时候，把里面的所有的 fc 的 pkg 改成相应的。即运行时我不看到 pkg，我全部运行完了再改，然后merge到现在的项目里

思考如何实现 F(id): (F(id) ) (x) = F(x) 

思考：如果 opt 是 作用在 s 上的，那 如果f,g是 s 上的函数，那 f opt g 也自动被定义了： (f opt g)(x) = f(x) opt g(x)： 即 F(f,g)(x) 相当于 F(f(x), g(x)) . 这里的 f 和 g 必须是 s 上的单元函数，然后opt是f和g的共同返回值的集合上的运算

但这可能和 F(f,g) 的 F 是 返回值是函数的函数 的形式矛盾了.
我觉得比较好的情况是，我 如果返回值是函数的函数，那我用额外的signal（以后再说）来定义，而默认情况，如果是函数套函数，那就是 F(f,g)(x) 这里的 f,g 是 集合 x 上的函数，F是 f和g的共同的返回值的集合上的运算

id 作为一个 内置的，能读入任何类型的参数的函数，送给了用户（类似=在prop里起到的作用：能读入任何类型的东西）；用户不允许重载函数名。

也可以每次定义一个集合的时候，自动引入 setName_id 这个函数，然后这个函数统一形如 
fn setName_id(x setName):
    setName_id(x) = x

