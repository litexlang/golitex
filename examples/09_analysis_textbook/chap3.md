```litex
# Analysis I, Chapter 3: Set theory.

# 把 Tao Chapter 3 的集合论主线翻译成
# Litex 的表达习惯。Chapter 3 里很多东西在 Litex 里已经是 builtin surface：
# `set`、`$in`、`$subset`、`finite_set`、`count`、tuple、Cartesian product、函数类型等。
# 所以这里的重点不是从空集公理重新构造集合论，而是解释原书里的概念在 Litex 里应该怎么用。
#
# 读这个文件时要区分两条线：checked Litex route 是当前 verifier 能直接检查的
# 表达；source route 是 Tao 书里的构造或证明思路。`abstract_prop`
# 只用于明确标记的背景接口；本文件不保留未证明假设。

# 用 """ """ 括起来的是原书对应位置的简短摘录；中文注释说明翻译决策；
# `sketch:` 用来放例子、证明骨架或者暂时只展示 proof idea 的地方。

"""
Definition 3.1.1 (Informal). We define a set A to be any unordered collection
of objects. If x is an object, we say that x is an element of A, written x in A.
"""

# 这里对应 Litex 的 builtin set surface。“是集合”这个谓词用 `set`，元素关系用 `$in`。

# Example
# 如果是有限列举集合，Litex 可以直接写 `{1, 2, 3}`。集合是 unordered 的，
# 所以 `{3, 8, 5, 2}` 和 `{2, 3, 5, 8}` 应该被看成同一个集合。
# by extension 表示 extension 公理（后面会提到），是用来证明集合相等的：集合A和B相等iff所有A的元素属于B，所有B的元素属于A
# by enumerate finite_set 的作用是用枚举法来证明集合中的元素的共有性质

sketch:
    by extension:
        ? {3, 8, 5, 2} = {2, 3, 5, 8}
        # `by enumerate finite_set` 相当于遍历 finite-set literal 里的所有元素。
        # 这里就是分别检查 x=3、x=8、x=5、x=2 时目标性质是否成立；
        # 每个 case 都成立后，就得到 `forall x {3, 8, 5, 2}: ...`。
        by enumerate finite_set:
            ? forall x {3, 8, 5, 2}:
                x $in {2, 3, 5, 8}
        by enumerate finite_set:
            ? forall y {2, 3, 5, 8}:
                y $in {3, 8, 5, 2}

    3 $in {1, 2, 3, 4, 5}
    not 7 $in {1, 2, 3, 4, 5}


"""
Example 3.1.2 (Informal). A set may contain another set as one of its
elements, for instance {3, {3, 4}, 4}. Not every object has to be regarded as
a set.
Remark 3.1.3. Pure set theory identifies every object with a set; this text
takes an agnostic position between pure and impure set theories.
"""

# 这个 example 说明两件事。第一，membership 是一层关系：`{3, 4}` 可以作为一个元素出现，
# 它不是自动被摊平成 3 和 4。第二，Litex 采用更 agnostic 的表面：数字、集合、函数都可以
# 作为数学对象参与表达；需要集合接口时用 `$is_set`、`$in`、`$subset` 等谓词说明。这里要突出一下litex的约定和tao书的一些不同（虽然运用起来没什么区别）
# 所以这里不把自然数强行构造成 von Neumann set，而是直接使用 Litex 的 builtin 对象。但用户可以自己用 by induc 来定义出来诺依曼定义下的自然数

"""
Axiom 3.1 (Sets are objects). If A is a set, then A is also an object.
"""

# Litex 里没有必要额外引入一个 Tao-specific 的 object 类型。`set` 已经可以作为
# 后续 membership、pair set、power set、Cartesian product 的对象来使用。
# 这一类 foundational axiom 在 sketch 里通常只解释，不单独做成 abstract_prop。
# 注意 `forall a set` 表达的是 `$is_set(a)`，不是说 a 属于“所有集合组成的集合”。
# Litex 的 `$is_set` 是工作接口：很多内置对象可以作为集合论表达里的对象使用。
# 这不是 Tao 对 object universe 的逐层构造；如果以后要重建 von Neumann naturals
# 或 pure-set universe，应作为另一条 source-route formalization，而不是本章主线。

sketch:
    forall x set, y R, z N:
        $is_set(x)
        $is_set(y) # 因为任何东西都是满足 is_set 的，所以它对。
        $is_set(z)

    $is_set(1) # 1 是东西，所以它对

"""
Example 3.1.5. Sets with the same members are equal even if the display order
or repeated entries differ.
"""

# 这个 example 是 extensional equality 的第一个具体检验。集合没有 first/last element，
# 重复写同一个对象也不改变 membership 状态；这就是下面 `by extension` 的意义。

"""
Definition 3.1.4 (Equality of sets). Two sets A and B are equal iff every
element of A is an element of B and vice versa.
"""

# 集合相等在 Litex 里用 `by extension`。证明目标是 A = B，
# 证明方法是分别证明 A 的任意元素在 B 里、B 的任意元素在 A 里。
# litex 用 by extension 关键词表示两个集合相等

sketch:
    by extension:
        ? {1, 2, 3, 4, 5} = {3, 4, 2, 1, 5}
        by enumerate finite_set:
            ? forall x {1, 2, 3, 4, 5}:
                x $in {3, 4, 2, 1, 5}
        by enumerate finite_set:
            ? forall y {3, 4, 2, 1, 5}:
                y $in {1, 2, 3, 4, 5}

# 在litex中所有东西x都满足$is_set(x)。
# 等号在litex有传递性，交换性，自己等于自己

forall A set:
    A = A

forall A, B set:
    A = B
    =>:
        B = A

forall A, B, C set:
    A = B
    B = C
    =>:
        A = C


"""
Axiom 3.2 (Empty set). There exists a set emptyset which contains no elements.
Lemma 3.1.6 (Single choice). Let A be a non-empty set. Then there exists an
object x such that x in A.
"""

# 空集和非空集合也都已经是 Litex 的 builtin surface。
# `have x A` 就是在非空类型/集合 A 中选择一个元素，这对应 Tao 的 single choice。

not $is_nonempty_set({})

claim:
    ? forall x set:
        not x $in {}
    by contra:
        ? not x $in {}
        x $in {}
        witness $is_nonempty_set({}) from x:
            x $in {}
        impossible not $is_nonempty_set({})

claim:
    ? forall A nonempty_set:
        exist x A st {x $in A}
    have x A
    witness exist x A st {x $in A} from x:
        x $in A

"""
Remark 3.1.7. Single choice lets us choose one element from one non-empty set;
finite choice and the full axiom of choice are stronger later principles.
Remark 3.1.8. The empty set is not the natural number 0, though its
cardinality is 0.
"""

# Litex 的 `have x A` 正是 single choice 的 proof move。它不是无限 choice：
# 从一族无限多个非空集合同时选元素需要 Chapter 8 的 choice interface。
# 另外 `{}` 和 `0` 在 Litex 里也是不同对象；`count({}) = 0` 只是在说 cardinality。

count({}) = 0

"""
Axiom 3.3 (Singleton sets and pair sets). If a and b are objects, then the
singleton set {a} and pair set {a,b} exist.
"""

# singleton/pair set 在 Litex 里直接用 `{a}`、`{a, b}`。
# 注意 displayed finite set 通常要求元素能被判断为不同；重复元素的退化情形
# `{a, a} = {a}` 更适合作为 set library 的 proof debt，而不是在这里包一层。

sketch:
    forall x set:
        x $in {x}

    1 $in {1, 2}
    2 $in {1, 2}

"""
Examples 3.1.10. From the empty set one can build {}, {{}}, {{{}}}, and
{{}, {{}}}; these are distinct set-shaped objects.
"""

# 这个 example 承接 Example 3.1.2：一个 set 可以作为另一个 set 的元素。样章里不重建
# pure set coding，只保留这个 nested-set intuition；后面真正需要 cardinality 时用
# `finite_set` 和 `count`。

sketch:
    count({}) = 0
    count({{}}) = 1
    count({{{}}}) = 1
    count({{}, {{}}}) = 2

    claim:
        ? {} != {{}}
        by contra:
            ? {} != {{}}
            {} = {{}}
            count({}) = count({{}})
            0 = count({}) = count({{}}) = 1
            impossible 0 = 1

    claim:
        ? {} != {{{}}}
        by contra:
            ? {} != {{{}}}
            {} = {{{}}}
            count({}) = count({{{}}})
            0 = count({}) = count({{{}}}) = 1
            impossible 0 = 1

    claim:
        ? {} != {{}, {{}}}
        by contra:
            ? {} != {{}, {{}}}
            {} = {{}, {{}}}
            count({}) = count({{}, {{}}})
            0 = count({}) = count({{}, {{}}}) = 2
            impossible 0 = 2

    claim:
        ? {{}} != {{{}}}
        by contra:
            ? {{}} != {{{}}}
            {{}} = {{{}}}
            {} $in {{}}
            {} $in {{{}}}
            {} = {{}}
            count({}) = count({{}})
            0 = count({}) = count({{}}) = 1
            impossible 0 = 1

    claim:
        ? {{}} != {{}, {{}}}
        by contra:
            ? {{}} != {{}, {{}}}
            {{}} = {{}, {{}}}
            count({{}}) = count({{}, {{}}})
            1 = count({{}}) = count({{}, {{}}}) = 2
            impossible 1 = 2

    claim:
        ? {{{}}} != {{}, {{}}}
        by contra:
            ? {{{}}} != {{}, {{}}}
            {{{}}} = {{}, {{}}}
            count({{{}}}) = count({{}, {{}}})
            1 = count({{{}}}) = count({{}, {{}}}) = 2
            impossible 1 = 2

"""
Axiom 3.4 (Pairwise union). x in A union B iff x in A or x in B.
Lemma 3.1.13. Union is commutative, associative, idempotent, and has empty set
as identity. If a and b are objects, then {a, b} = {a} union {b}.
"""

# union 用 builtin `union(A, B)`。先写 Axiom 3.4 的通用 membership interface：
# 任意对象 x 在 union(A, B) 里，当且仅当 x 在 A 里或者在 B 里。
# 后面的 `{1, 2} union {2, 3}` 只是这个 general rule 的 concrete example。

forall A, B set, x set:
    x $in union(A, B)
    =>:
        x $in A or x $in B

forall A, B set, x set:
    x $in A
    =>:
        x $in union(A, B)

forall A, B set, x set:
    x $in B
    =>:
        x $in union(A, B)

sketch:
    1 $in union({1, 2}, {2, 3})
    2 $in union({1, 2}, {2, 3})
    3 $in union({1, 2}, {2, 3})
    $is_finite_set(union({1, 2}, {2, 3}))
    count(union({1, 2}, {2, 3})) <= count({1, 2}) + count({2, 3})

"""
Example 3.1.11. {1, 2} union {2, 3} is {1, 2, 3}.
Remark 3.1.12. Union is well-defined under equality of sets.
Remark 3.1.14. Union resembles addition in some ways, but it is a set
operation, not numerical addition.
"""

# Remark 3.1.12 是 substitution discipline：如果 A = A'，那么 union(A, B) =
# union(A', B)。Remark 3.1.14 则提醒不要把 `{2} union {3}` 和 `2 + 3` 混起来；
# Litex 的类型 surface 会把这两种操作分开。

sketch:
    by extension:
        ? union({1, 2}, {2, 3}) = {1, 2, 3}
        claim:
            ? forall x union({1, 2}, {2, 3}):
                x $in {1, 2, 3}
            x $in union({1, 2}, {2, 3})
            x $in {1, 2} or x $in {2, 3}
            by cases:
                ? x $in {1, 2, 3}
                case x $in {1, 2}:
                    x = 1 or x = 2
                    by cases:
                        ? x $in {1, 2, 3}
                        case x = 1:
                            x $in {1, 2, 3}
                        case x = 2:
                            x $in {1, 2, 3}
                case x $in {2, 3}:
                    x = 2 or x = 3
                    by cases:
                        ? x $in {1, 2, 3}
                        case x = 2:
                            x $in {1, 2, 3}
                        case x = 3:
                            x $in {1, 2, 3}
        by enumerate finite_set:
            ? forall y {1, 2, 3}:
                y $in union({1, 2}, {2, 3})

    forall A, A1, B, B1 set:
        A = A1
        B = B1
        =>:
            union(A, B) = union(A1, B1)
    by extension:
        ? union({2}, {3}) = {2, 3}
        claim:
            ? forall x union({2}, {3}):
                x $in {2, 3}
            x $in union({2}, {3})
            x $in {2} or x $in {3}
            by cases:
                ? x $in {2, 3}
                case x $in {2}:
                    x = 2
                    x $in {2, 3}
                case x $in {3}:
                    x = 3
                    x $in {2, 3}
        by enumerate finite_set:
            ? forall y {2, 3}:
                y $in union({2}, {3})

    count(union({2}, {3})) = count({2, 3}) = 2
    2 + 3 = 5

    # Tao 的完整句子是 “if a and b are objects, {a,b} = {a} union {b}”，允许
    # a = b 时退化成 `{a} = union({a}, {a})`。当前 Litex 的 `{a,b}` literal
    # 要求能证明 `a != b`，所以 unrestricted pair-set constructor 仍是 proof_debt。
    claim:
        ? forall a, b set:
            a != b
            =>:
                {a, b} = union({a}, {b})
        by extension:
            ? {a, b} = union({a}, {b})
            claim:
                ? forall x {a, b}:
                    x $in union({a}, {b})
                x = a or x = b
                by cases:
                    ? x $in union({a}, {b})
                    case x = a:
                        x $in {a}
                        x $in union({a}, {b})
                    case x = b:
                        x $in {b}
                        x $in union({a}, {b})
            claim:
                ? forall y union({a}, {b}):
                    y $in {a, b}
                y $in union({a}, {b})
                y $in {a} or y $in {b}
                by cases:
                    ? y $in {a, b}
                    case y $in {a}:
                        y = a
                        y $in {a, b}
                    case y $in {b}:
                        y = b
                        y $in {a, b}

    forall A, B set:
        union(A, B) = union(B, A)

    forall A, B, C set:
        union(union(A, B), C) = union(A, union(B, C))

    forall A set:
        union(A, A) = A
        union(A, {}) = A
        union({}, A) = A

"""
Definition 3.1.15 (Subsets). A subset of B iff every element of A is also an
element of B.
Proposition 3.1.18. Sets are partially ordered by set inclusion.
"""

# `A $subset B` 就是 subset。它有两个方向的 interface：
# elimination 是从 `A $subset B` 和 `x A` 读出 `x $in B`；
# introduction 是先证明 `forall x A: x $in B`，再把这个 forall 折叠成 `A $subset B`。
# antisymmetry 则回到 `by extension`：两个方向的 subset 合起来给出集合相等。

forall A, B set, x A:
    A $subset B
    =>:
        x $in B

forall A, B set:
    forall x A:
        x $in B
    =>:
        A $subset B

# 上面这个 claim 是 subset introduction 的 proof shape：如果当前 proof context 里已经
# 有 `forall x A: x $in B`，下一行 `A $subset B` 就是 Definition 3.1.15 的折叠形式。

forall A set:
    A $subset A

# 这一步是 subset 的 transitivity。因为 `$subset` 是 Litex builtin relation，
# verifier 已经知道它是 transitive：从 `A $subset B` 和 `B $subset C` 可以直接推出
# `A $subset C`。

forall A, B, C set:
    A $subset B
    B $subset C
    =>:
        A $subset C

# 如果是用户自己定义的二元 prop，就用 `by transitive_prop:` 注册传递性。
# 它要求 prove block 形如 `$p(x,y), $p(y,z) => $p(x,z)`；注册后，
# Litex 就能把同一个 prop 的链式事实自动闭包到首尾。

sketch:
    prop same_set_for_transitive_prop_example(x, y set):
        x = y

    by transitive_prop:
        ? forall x, y, z set:
            $same_set_for_transitive_prop_example(x, y)
            $same_set_for_transitive_prop_example(y, z)
            =>:
                $same_set_for_transitive_prop_example(x, z)
        x = y
        y = z
        x = z

    forall a, b, c set:
        $same_set_for_transitive_prop_example(a, b)
        $same_set_for_transitive_prop_example(b, c)
        =>:
            $same_set_for_transitive_prop_example(a, c)

    claim:
        ? forall A, B set:
            A $subset B
            B $subset A
            =>:
                A = B
        by extension:
            ? A = B

"""
Remark 3.1.16. Subset is also well-defined under equality of sets.
Examples 3.1.17. {1, 2, 4} is a proper subset of {1, 2, 3, 4, 5}; every set
is a subset of itself, and the empty set is a subset of every set.
"""

# Remark 3.1.16 是 equality substitution：替换相等的左右集合，不改变 subset 命题。
# proper subset 在 Litex 里通常写成 `A $subset B` 加 `A != B`。

sketch:
    forall A, A1, B, B1 set:
        A = A1
        B = B1
        A $subset B
        =>:
            A1 $subset B1
    by enumerate finite_set:
        ? forall x {1, 2, 4}:
            x $in {1, 2, 3, 4, 5}

    {1, 2, 4} $subset {1, 2, 3, 4, 5}
    {1, 2, 4} != {1, 2, 3, 4, 5}

    claim:
        ? forall A set:
            {} $subset A
        claim:
            ? forall x {}:
                x $in A
            by contra:
                ? x $in A
                not $is_nonempty_set({})
                witness $is_nonempty_set({}) from x
                impossible $is_nonempty_set({})
        {} $subset A

    claim:
        ? forall A, B set:
            A $subset B
            A != B
            =>:
                exist x B st {not x $in A}
        by contra:
            ? exist x B st {not x $in A}
            forall x B:
                x $in A
            by extension:
                ? A = B
            impossible A != B

"""
Remark 3.1.19. Subsets and unions are related by elementary set laws.
Remark 3.1.20. Set inclusion is only a partial order, unlike the total order
on natural numbers.
Remark 3.1.21. Membership `$in` and subset `$subset` are different relations.
"""

# 这三个 remark 都是避免误读 notation。`2 $in {1, 2, 3}` 是元素关系；
# `{2} $subset {1, 2, 3}` 是集合之间的包含关系。两个集合也可以不可比较：
# 比如偶数集和奇数集都不是对方的 subset。

sketch:
    {1} $subset union({1}, {2, 3})
    {2, 3} $subset union({1}, {2, 3})

    claim:
        ? union({1}, {2, 3}) $subset {1, 2, 3}
        claim:
            ? forall x union({1}, {2, 3}):
                x $in {1, 2, 3}
            x $in union({1}, {2, 3})
            x $in {1} or x $in {2, 3}
            by cases:
                ? x $in {1, 2, 3}
                case x $in {1}:
                    x = 1
                    x $in {1, 2, 3}
                case x $in {2, 3}:
                    x = 2 or x = 3
                    by cases:
                        ? x $in {1, 2, 3}
                        case x = 2:
                            x $in {1, 2, 3}
                        case x = 3:
                            x $in {1, 2, 3}
        union({1}, {2, 3}) $subset {1, 2, 3}

    claim:
        ? not {1} $subset {2}
        by contra:
            ? not {1} $subset {2}
            {1} $subset {2}
            1 $in {1}
            1 $in {2}
            not 1 $in {2}
            impossible not 1 $in {2}

    claim:
        ? not {2} $subset {1}
        by contra:
            ? not {2} $subset {1}
            {2} $subset {1}
            2 $in {2}
            2 $in {1}
            not 2 $in {1}
            impossible not 2 $in {1}

    1 <= 2

    2 $in {1, 2, 3}
    {2} $subset {1, 2, 3}

"""
Axiom 3.5 (Axiom of specification). From a set A and a property P(x), form the
subset {x in A : P(x)}.
"""

# specification 在 Litex 里可以写成 set comprehension，例如 `{n N: n < 4}`。
# 当 `n $in {k N: k < 4}` 作为条件出现时，Litex 会自动把这个 membership
# 展开成 ambient type 和 predicate：这里就是 `n $in N` 与 `n < 4`。

sketch:
    have small_initial_segment set = {n N: n < 4}

    forall n N:
        n $in {k N: k < 4}
        =>:
            n < 4
    forall x set:
        x $in {k N: k < 4}
        =>:
            x $in N
    forall x set:
        x $in {k N: k < 4}
        =>:
            x < 4
    forall n N:
        n < 4
        =>:
            n $in {k N: k < 4}
"""
Example 3.1.22. If S = {1, 2, 3, 4, 5}, then {n in S : n < 4} is
{1, 2, 3}; the predicates n < 7 and n < 1 give S and the empty set.
"""

# 这正是 Litex set comprehension 的用途：先指定 ambient set/type，再写筛选条件。

sketch:
    1 $in {n N: n $in {1, 2, 3, 4, 5} and n < 4}
    2 $in {n N: n $in {1, 2, 3, 4, 5} and n < 4}
    3 $in {n N: n $in {1, 2, 3, 4, 5} and n < 4}

    claim:
        ? not 4 $in {n N: n $in {1, 2, 3, 4, 5} and n < 4}
        by contra:
            ? not 4 $in {n N: n $in {1, 2, 3, 4, 5} and n < 4}
            4 $in {n N: n $in {1, 2, 3, 4, 5} and n < 4}
            4 < 4
            not 4 < 4
            impossible not 4 < 4

    claim:
        ? not 5 $in {n N: n $in {1, 2, 3, 4, 5} and n < 4}
        by contra:
            ? not 5 $in {n N: n $in {1, 2, 3, 4, 5} and n < 4}
            5 $in {n N: n $in {1, 2, 3, 4, 5} and n < 4}
            5 < 4
            not 5 < 4
            impossible not 5 < 4

    5 $in {n N: n $in {1, 2, 3, 4, 5} and n < 7}

    claim:
        ? not 1 $in {n N: n $in {1, 2, 3, 4, 5} and n < 1}
        by contra:
            ? not 1 $in {n N: n $in {1, 2, 3, 4, 5} and n < 1}
            1 $in {n N: n $in {1, 2, 3, 4, 5} and n < 1}
            1 < 1
            not 1 < 1
            impossible not 1 < 1

"""
Definition 3.1.23 (Intersections). An element is in A intersect B iff it is in
A and in B.
"""

# `intersect(A, B)` 是 Litex 的交集函数。它的定义性用法是双向的：
# 从 `x $in intersect(A, B)` 可以拆出 `x $in A` 和 `x $in B`；
# 反过来，有这两个 membership 也能构造 `x $in intersect(A, B)`。

forall A, B set, x set:
    x $in intersect(A, B)
    =>:
        x $in A
        x $in B

forall A, B set, x set:
    x $in A
    x $in B
    =>:
        x $in intersect(A, B)

"""
Remark 3.1.24. Intersection is well-defined because it is defined by
membership and equality.
Examples 3.1.25. Concrete intersections include {1, 2, 4} intersect
{2, 3, 4} = {2, 4}, and disjoint intersections are empty.
Remark 3.1.26. The English word "and" can mean union, intersection, or
addition depending on context; mathematical symbols remove that ambiguity.
"""

# 这些 examples/remarks 对应 Litex 的 `intersect`、`union`、`+` 三个不同符号。
# 使用符号的好处就是不会把“boys and girls”的 union 和“single and male”的 intersection 混掉。

sketch:
    2 $in intersect({1, 2, 4}, {2, 3, 4})
    4 $in intersect({1, 2, 4}, {2, 3, 4})
    $is_finite_set(intersect({1, 2, 4}, {2, 3, 4}))
    count(intersect({1, 2, 4}, {2, 3, 4})) <= count({1, 2, 4})
    intersect({1, 2, 4}, {2, 3, 4}) = {2, 4}
    count(intersect({1, 2, 4}, {2, 3, 4})) = count({2, 4}) = 2
    not 1 $in intersect({1, 2, 4}, {2, 3, 4})
    intersect({1}, {2}) = {}

"""
Definition 3.1.27 (Difference sets). An element is in A minus B iff it is in A
and not in B.
Proposition 3.1.28. Intersections, differences, and unions obey the usual
Boolean set laws.
"""

# `set_minus(A, B)` 是 Litex 的差集函数。和 intersect 一样，membership 会自动
# 展开成定义中的条件；反向也可以从这些条件构造 membership。

forall A, B set, x set:
    x $in set_minus(A, B)
    =>:
        x $in A
        not x $in B
forall A, B set, x set:
    x $in A
    not x $in B
    =>:
        x $in set_minus(A, B)
$is_finite_set(set_minus({1, 2, 3}, {2}))
count(set_minus({1, 2, 3}, {2})) <= count({1, 2, 3})

forall A, B set:
    intersect(A, B) = intersect(B, A)

forall A, B, C set:
    intersect(intersect(A, B), C) = intersect(A, intersect(B, C))

forall A, B, C set:
    intersect(A, union(B, C)) = union(intersect(A, B), intersect(A, C))

forall A, B, C set:
    set_minus(A, union(B, C)) = intersect(set_minus(A, B), set_minus(A, C))

forall A, B, C set:
    set_minus(A, intersect(B, C)) = union(set_minus(A, B), set_minus(A, C))

"""
Remark 3.1.29. The de Morgan laws are basic Boolean/set laws.
Remark 3.1.30. Complementation exchanges unions with intersections and
reveals a duality between the whole ambient set and the empty set.
"""

# 上面两条 `set_minus` 公式就是有限 de Morgan law 的 Litex surface。
# 更一般的 indexed union/intersection 版本留给后面的 set theory / choice API。

"""
Axioms 3.6-3.9. Replacement, infinity, regularity, and restrictions on
universal specification.
"""

"""
Axiom 3.6 (Replacement). If a binary relation P assigns at most one output y
to each input x in a set A, then the P-image of A is itself a set.  In Litex
this source axiom is represented by the object `replacement(P, A)`.
"""

# Axiom 3.6 is now an object-level interface.  The first argument is the
# relation name, and the second argument is the source set.  The object is
# well-defined only after a uniqueness fact for the relation over the source
# set is available.  Membership in the replacement set gives the preimage witness.


"""
Examples 3.1.31-3.1.32. Replacement sends each element of {3, 5, 9} through a
rule such as x |-> x + 1, producing {4, 6, 10}; a constant rule can collapse
several inputs to the singleton {1}.
Example 3.1.33 (Informal). Two set-builder expressions may define the same
set even when their displayed element formulas differ pointwise.
"""

# Axiom 3.6 is the set-existence principle behind replacement. In Litex this can be
# written directly as `replacement(P, A)` when `P` is a binary relation that is
# functional on A. Membership in the replacement set gives a preimage witness.

sketch:
    prop plus_one_relation(x R, y R):
        y = x + 1

    # This is the functional/uniqueness proof required by `replacement`.
    claim:
        prove:
            forall x {3, 5, 9}, y, y2 set:
                $plus_one_relation(x, y)
                $plus_one_relation(x, y2)
                =>:
                    y = y2
        y = x + 1
        y2 = x + 1
        y = y2

    have replacement_plus_one_image set = replacement(plus_one_relation, {3, 5, 9})

# 一个更接近后面 Cartesian product 语言的例子是：取
# `A = closed_range(1, n)`，`c` 是 n 维 cart。若想得到
# `{y: exist x A st {y $in proj(c, x)}}`，直接令 `P(x,y)` 为
# `y $in proj(c,x)` 一般不满足 Replacement 的 uniqueness 条件：固定一个
# coordinate x 后，第 x 个 factor 里通常有很多 y。
#
# 正确的 set-theoretic route 是两步：先用 Replacement 收集每个 projection
# factor set，再对这个 set of factor sets 取 `cup`。也就是说，Replacement
# 应用于 functional relation `Q(x, S)`，它表示 `S = proj(c, x)`；然后
# `y $in cup(replacement(Q, A))` 表示存在某个 x in A，使得 y 属于第 x 个
# projection factor。
#
# 目前 Litex 的 `proj(c, x)` 要求 projection dimension 是具体数字，所以不把泛型
# variable-index 版本写成 checked block。下面的 3 维例子用具体 projection、
# `fn_range_on` 和 `cup` 给出同一个想法的可检查 surface。

sketch:
    have C set = cart({1, 2}, {3, 4}, {5, 6})
    $is_cart(C)
    cart_dim(C) = 3
    proj(C, 1) = {1, 2}
    proj(C, 2) = {3, 4}
    proj(C, 3) = {5, 6}

    have fn projection_factor_on_three(k {1, 2, 3}) {{1, 2}, {3, 4}, {5, 6}} by cases:
        case k = 1: proj(C, 1)
        case k = 2: proj(C, 2)
        case k = 3: proj(C, 3)

    projection_factor_on_three(1) = proj(C, 1) = {1, 2}
    projection_factor_on_three(2) = proj(C, 2) = {3, 4}
    projection_factor_on_three(3) = proj(C, 3) = {5, 6}
    projection_factor_on_three(1) $in fn_range_on(projection_factor_on_three, {1, 2, 3})
    projection_factor_on_three(2) $in fn_range_on(projection_factor_on_three, {1, 2, 3})
    projection_factor_on_three(3) $in fn_range_on(projection_factor_on_three, {1, 2, 3})
    {1, 2} $in fn_range_on(projection_factor_on_three, {1, 2, 3})
    {3, 4} $in fn_range_on(projection_factor_on_three, {1, 2, 3})
    {5, 6} $in fn_range_on(projection_factor_on_three, {1, 2, 3})

    1 $in {1, 2}
    3 $in {3, 4}
    5 $in {5, 6}
    1 $in projection_factor_on_three(1)
    3 $in projection_factor_on_three(2)
    5 $in projection_factor_on_three(3)
    witness exist k {1, 2, 3} st {1 $in projection_factor_on_three(k)} from 1:
        1 $in projection_factor_on_three(1)
    witness exist k {1, 2, 3} st {3 $in projection_factor_on_three(k)} from 2:
        3 $in projection_factor_on_three(2)
    1 $in cup(fn_range_on(projection_factor_on_three, {1, 2, 3}))
    3 $in cup(fn_range_on(projection_factor_on_three, {1, 2, 3}))
    5 $in cup(fn_range_on(projection_factor_on_three, {1, 2, 3}))
    fn_range_on(projection_factor_on_three, {1, 2, 3}) $subset {{1, 2}, {3, 4}, {5, 6}}
    $is_finite_set(fn_range_on(projection_factor_on_three, {1, 2, 3}))

# For ordinary function images, Litex also has the convenient `fn_range_on(f, A)`
# interface. This is the common checked route when the relation is already represented
# by a function.
sketch:
    have fn plus_one_on_three(n {3, 5, 9}) {4, 6, 10} by cases:
        case n = 3: 4
        case n = 5: 6
        case n = 9: 10

    plus_one_on_three(3) = 4
    plus_one_on_three(5) = 6
    plus_one_on_three(9) = 10

    plus_one_on_three(3) $in fn_range_on(plus_one_on_three, {3, 5, 9})
    plus_one_on_three(5) $in fn_range_on(plus_one_on_three, {3, 5, 9})
    plus_one_on_three(9) $in fn_range_on(plus_one_on_three, {3, 5, 9})
    fn_range_on(plus_one_on_three, {3, 5, 9}) $subset {4, 6, 10}
    $is_finite_set(fn_range_on(plus_one_on_three, {3, 5, 9}))

    have fn constant1_on_three(n {3, 5, 9}) {1} by cases:
        case n = 3: 1
        case n = 5: 1
        case n = 9: 1

    constant1_on_three(3) = 1
    constant1_on_three(5) = 1
    constant1_on_three(9) = 1
    constant1_on_three(3) $in fn_range_on(constant1_on_three, {3, 5, 9})
    1 $in fn_range_on(constant1_on_three, {3, 5, 9})

    claim:
        ? forall y fn_range_on(constant1_on_three, {3, 5, 9}):
            y $in {1}
        y $in fn_range_on(constant1_on_three, {3, 5, 9})
        have by preimage k from y $in fn_range_on(constant1_on_three, {3, 5, 9})
        k $in {3, 5, 9}
        y = constant1_on_three(k)
        constant1_on_three(k) $in {1}
        constant1_on_three(k) = 1
        y = 1
        y $in {1}

    fn_range_on(constant1_on_three, {3, 5, 9}) $subset {1}

    claim:
        ? forall y {1}:
            y $in fn_range_on(constant1_on_three, {3, 5, 9})
        y = 1
        1 $in fn_range_on(constant1_on_three, {3, 5, 9})
        y $in fn_range_on(constant1_on_three, {3, 5, 9})

    {1} $subset fn_range_on(constant1_on_three, {3, 5, 9})

    by extension:
        ? fn_range_on(constant1_on_three, {3, 5, 9}) = {1}

    count(fn_range_on(constant1_on_three, {3, 5, 9})) = count({1}) = 1

"""
Axiom 3.7 (Infinity). There is a set N of natural numbers containing 0 and
closed under successor, with the Peano axioms from Chapter 2.
"""

# Litex's builtin `N` is the chapter-facing infinity interface.  Chapter 2
# records the Peano facts; here we keep the set-existence role visible.

0 $in N

have fn successor_on_N(n N) N = n + 1

forall n N:
    successor_on_N(n) $in N

"""
Axiom 3.9 (Restriction on universal specification). Specification forms
subsets of an already-given set; there is no unrestricted universal set of
all objects.
"""

# Litex set builders have the same discipline: `{x A: ...}` needs an ambient
# set `A`.  The no-universal-set principle is illustrated by a concrete
# contradiction instead of pretending that `{x set: ...}` is a valid set builder.

prop is_universal_set(U set):
    forall x set:
        x $in U

# Axiom 3.9 rules out the universal-set idea behind unrestricted
# specification.  If U contained every set, then U would contain itself; applying
# regularity to the singleton {U} gives a disjoint member, contradiction.

claim:
    prove:
        forall U set:
            not $is_universal_set(U)
    by contra:
        prove:
            not $is_universal_set(U)
        $is_universal_set(U)
        U $in U
        U $in {U}
        by regularity_axiom({U})
        have by exist x {U} st {intersect(x, {U}) = {}}: x
        x = U
        intersect(x, {U}) = {}
        intersect(U, {U}) = intersect(x, {U}) = {}
        U $in intersect(U, {U})
        U $in {}
        not U $in {}
        impossible not U $in {}

sketch:
    by contra:
        prove:
            not $is_universal_set({1, 2})
        $is_universal_set({1, 2})
        3 $in {1, 2}
        not 3 $in {1, 2}
        impossible not 3 $in {1, 2}

    2 $in {n N: n < 4}
    2 $in {n N: n + 1 < 5}

    claim:
        ? not 5 $in {n N: n < 4}
        by contra:
            ? not 5 $in {n N: n < 4}
            5 $in {n N: n < 4}
            5 < 4
            not 5 < 4
            impossible not 5 < 4

    claim:
        ? not 5 $in {n N: n + 1 < 5}
        by contra:
            ? not 5 $in {n N: n + 1 < 5}
            5 $in {n N: n + 1 < 5}
            5 + 1 < 5
            not 5 + 1 < 5
            impossible not 5 + 1 < 5


# Analysis I, Chapter 3, Section 3.3: Functions.
#
# 样章分节：这一节把 Tao 的函数语言翻译成 Litex 的函数 surface。
# 用 """ """ 定位原书中的 definition/example/remark；中文注释解释为什么这样
# 对应到 Litex；`sketch:` 用来放教学例子、局部证明骨架和 follow-up notes。



"""
Definition 3.3.1 (Functions). Let X,Y be sets, and let P(x,y) be a property
for x in X and y in Y. If every x in X has exactly one y in Y satisfying
P(x,y), then P defines a function f : X -> Y. Thus y=f(x) iff P(x,y).
"""

# 这条 definition 的主体不是“函数值落在 codomain 里”这个 sanity check，
# 而是 vertical line test 和 defining equivalence：
#
#     forall x X: exist! y Y st {P(x,y)}
#     y = f(x)  <=>  P(x,y)
#
# Litex 对应 `have fn ... as set`：从唯一存在定理创建函数。代码先用一个
# concrete finite graph 展示 relation 怎样变成函数；然后用 `abstract_prop P`
# 和 `relation_has_unique_output` 把同一个结构抽成 template。后面的 claims
# 检查 Tao 的 defining equivalence 的两个方向。最后再给一个
# graph-style relation 作为可直接看的例子。

sketch:
    have X_example set = {1, 2, 3}
    have Y_example set = {1, 2, 3}

    prop P_example(x X_example, y Y_example):
        y = x

    claim:
        prove:
            forall x X_example:
                exist! y Y_example st {$P_example(x, y)}
        witness exist! y Y_example st {$P_example(x, y)} from x

    have fn f_from_relation as set:
        ? forall x X_example:
            exist! y Y_example st {$P_example(x, y)}
        exist! y Y_example st {$P_example(x, y)}

    forall x X_example:
        $P_example(x, f_from_relation(x))

    forall x X_example, y Y_example:
        $P_example(x, y)
        =>:
            y = f_from_relation(x)
    claim:
        ? forall x X_example, y Y_example:
            y = f_from_relation(x)
            =>:
                $P_example(x, y)
        $P_example(x, f_from_relation(x))
        $P_example(x, y)

    abstract_prop P(x, y)

    prop relation_has_unique_output(X, Y set):
        forall x X:
            exist! y Y st {$P(x, y)}

    # `have fn ... as set` creates one function only after the domain X and
    # codomain Y have been fixed. `template` packages the same construction as
    # a family: for any X,Y satisfying the vertical line test, Litex can build
    # the corresponding function. This is the same reason that a sequence type
    # such as `fn(x N_pos) s` is useful uniformly for every target set s: after
    # s is supplied, it becomes an ordinary function type, but the pattern is a
    # family indexed by s.
    template<X set, Y set: $relation_has_unique_output(X, Y)>:
        have fn f_from_P as set:
            ? forall x X:
                exist! y Y st {$P(x, y)}
            exist! y Y st {$P(x, y)}

    forall X, Y set, x X:
        $relation_has_unique_output(X, Y)
        =>:
            $P(x, \f_from_P<X, Y>(x))
    forall X, Y set, x X, y Y:
        $relation_has_unique_output(X, Y)
        $P(x, y)
        =>:
            y = \f_from_P<X, Y>(x)
    claim:
        ? forall X, Y set, x X, y Y:
            $relation_has_unique_output(X, Y)
            y = \f_from_P<X, Y>(x)
            =>:
                $P(x, y)
        $P(x, \f_from_P<X, Y>(x))
        $P(x, y)

    # A concrete graph-style definition with P(x,y) specialized to y=x.
    have A set = R

    have fn graph_identity as set:
        ? forall x A:
            exist! y A st {y = x}
        witness exist! y A st {y = x} from x

    forall x A:
        graph_identity(x) = x

"""
Example 3.3.2. With X=N, Y=N, and P(x,y) the relation y=x++, the vertical
line test defines the increment function f:N->N. The attempted decrement
g:N->N from y++=x fails at x=0; restricting the domain to N\{0} gives a
valid predecessor function h:N\{0}->N.
"""

# 这个 example 也要先翻译 relation 本体。`y=x++` 在 Litex 里就是
# `y = x + 1`，所以先证明每个 x 有唯一 y，再用 `have fn ... as set`
# 定义出 increment。后面的 direct formula 是日常 Litex 写法。
#
# `N -> N` 的 decrement 不写成形式化函数：它在 0 处没有 output。这个反例有
# 教学意义，所以保留成 comment。限制到 `N_pos` 后，predecessor 可以真实定义。

sketch:
    claim:
        ? forall x N:
            exist! y N st {y = x + 1}
        witness exist y N st {y = x + 1} from x + 1:
            x + 1 $in N
        forall y1, y2 N:
            y1 = x + 1
            y2 = x + 1
            =>:
                y1 = y2
        exist! y N st {y = x + 1}

    have fn increment_from_relation as set:
        ? forall x N:
            exist! y N st {y = x + 1}
        exist! y N st {y = x + 1}

    forall x N:
        increment_from_relation(x) = x + 1

    increment_from_relation(4) = 5

    forall n N:
        increment_from_relation(2 * n + 3) = (2 * n + 3) + 1 = 2 * n + 4

    have fn increment_N(n N) N = n + 1
    have fn succ(n N) N_pos = n + 1

    increment_N(4) = 5
    increment_N(2 * 3 + 3) = 10
    succ(0) = 1

    # The all-domain decrement relation `y + 1 = x` is not a function
    # N -> N, because at x=0 there is no natural y with y+1=0.

    claim:
        ? forall a N_pos:
            exist! b N st {b + 1 = a}
        a >= 1
        a - 1 >= 0
        a - 1 $in N
        witness exist b N st {b + 1 = a} from a - 1:
            (a - 1) + 1 = a
        forall b1, b2 N:
            b1 + 1 = a
            b2 + 1 = a
            =>:
                b1 + 1 = b2 + 1
                b1 = (b1 + 1) - 1 = (b2 + 1) - 1 = b2
        exist! b N st {b + 1 = a}

    have fn pred_pos_from_relation as set:
        ? forall a N_pos:
            exist! b N st {b + 1 = a}
        exist! b N st {b + 1 = a}

    have fn pred_pos(n N_pos) N = n - 1

    pred_pos(1) = 0
    pred_pos(4) = 3
    succ(pred_pos(4)) = 4

"""
Litex 专栏：定义函数的几种语句。
"""

# 这个专栏不是 Tao 的新定义，而是把本节用到的 Litex function syntax 集中列出来。
# 读者先看上面的 source-facing vertical line test；这里再看日常写函数的几种方式。
#
# 1. `have fn f(x S) T = expr`：直接用公式定义函数。
# 2. `have fn f(x S, y T) U = expr`：多输入函数。
# 3. `have fn f(x S: condition) T = expr`：限制输入 domain 的函数。
# 4. `have fn f(...) T by cases:`：按条件分段定义函数。
# 5. `have fn f(...) T by induc ...:`：递归/归纳定义函数。
# 6. `have fn as algo f(...) T = expr`：定义可 `eval` 的算法函数。
# 7. `have fn f as set:`：从 `forall x: exist! y ...` 的唯一存在关系定义函数。
# 8. `'(x S) T {expr}`：匿名函数；适合临时传入或临时应用。
# 9. `f fn(x S) T`：这不是定义函数，而是在 theorem/claim 里声明一个函数参数。

sketch:
    have fn direct_succ(n N) N = n + 1
    direct_succ(4) = 5

    have fn add_two_inputs(x N, y N) N = x + y
    add_two_inputs(2, 3) = 5

    have fn restricted_pred(n N_pos) N = n - 1
    restricted_pred(4) = 3

    have fn max_by_cases(x, y R) R by cases:
        case x > y: x
        case x <= y: y

    max_by_cases(5, 3) = 5
    max_by_cases(2, 7) = 7

    have fn rec_add_one(n Z: n >= 0) R by induc n from 0:
        case n = 0: 1
        case n > 0: rec_add_one(n - 1) + 1

    rec_add_one(0) = 1
    rec_add_one(1) = rec_add_one(0) + 1 = 2

    have fn as algo algo_square(x R) R = x^2

    eval algo_square(3)
    algo_square(3) = 9

    have A set = R
    have B set = R

    have fn identity_from_unique_existence as set:
        ? forall x A:
            exist! y B st {y = x}
        witness exist! y B st {y = x} from x

    forall x A:
        identity_from_unique_existence(x) = x

    '(x N) N {x + 1}(4) = 5

    claim:
        ? forall S, T set, f fn(x S) T, x S:
            f(x) $in T
        f(x) $in T

"""
Example 3.3.3. The relation y^2=x does not define a square-root function
R->R: negative inputs have no output, and positive inputs can have two outputs.
After restricting the domain and range to nonnegative reals, it becomes a
valid implicit definition.
"""

# Chapter 5 will introduce the real interval vocabulary needed for a polished
# nonnegative square-root interface. The source-facing point here is relation
# failure: `y^2=x` may fail existence or uniqueness. The negative-input
# obstruction is proved by contradiction from the built-in nonnegativity of
# squares; uniqueness fails because both 2 and -2 square to 4.

sketch:
    by contra:
        ? not exist y R st {y^2 = -1}
        have by exist y R st {y^2 = -1}: a
        a^2 >= 0
        a^2 = -1
        impossible -1 >= 0

    2^2 = 4
    (-2)^2 = 4
    2 != -2

"""
Example 3.3.4. The relation P(x,y) defined by y=7 passes the vertical line
test and gives the constant function N->N with value 7.
"""

# 这和 Example 3.3.2 一样：先翻译 relation `y=7`，再给出日常 direct function
# 写法。这个例子也说明不同 input 可以有同一个 output。

sketch:
    claim:
        ? forall x N:
            exist! y N st {y = 7}
        witness exist y N st {y = 7} from 7:
            7 $in N
        forall y1, y2 N:
            y1 = 7
            y2 = 7
            =>:
                y1 = y2
        exist! y N st {y = 7}

    have fn constant7_from_relation as set:
        ? forall x N:
            exist! y N st {y = 7}
        exist! y N st {y = 7}

    forall x N:
        constant7_from_relation(x) = 7

    have fn constant7_N(n N) N = 7

    constant7_N(0) = 7
    constant7_N(12) = 7

    0 != 12
    constant7_N(0) = constant7_N(12)

"""
After these examples, Tao distinguishes explicit definitions, implicit
definitions, and the danger of suppressing domain and codomain.
"""

# 普通 Litex 代码更常用 direct formula、case split、recursive definition、
# algo definition 和 anonymous function；这些是 Definition 3.3.1 之后的
# usability layer，不能替代上面的 source-facing vertical-line definition。

sketch:
    abs(2) = 2
    abs(-2) = 2
    -2 != 2

    have fn self_max(x, y R) R by cases:
        case x > y: x
        case x <= y: y

    self_max(5, 3) = 5
    self_max(2, 7) = 7

    have fn rec_add_one(n Z: n >= 0) R by induc n from 0:
        case n = 0: 1
        case n > 0: rec_add_one(n - 1) + 1

    rec_add_one(0) = 1

    have fn as algo algo_identity(x R) R = x

    eval algo_identity(3)
    algo_identity(3) = 3

    '(x N) N {x + 1}(4) = 5

"""
Remark 3.3.5. Parentheses are overloaded: they can group operations, hold a
function argument, or hold a property argument. Context disambiguates them.
"""

# Litex 中 `f(x)` 是函数应用，`(x,y)` 是 tuple，`x * (y+z)` 是乘法表达式；
# 它们靠语法位置区分。

"""
Remark 3.3.6. Functions are objects, but they are not sets; a function can be
represented by its graph later.
"""

# 这条 remark 不需要证明成 theorem。Section 3.5 会用 Cartesian product 解释
# graph `{(x,f(x)): x in X}`，但这里先保留“函数不是集合”的 source distinction。



"""
Definition 3.3.7. Two functions with the same domain and codomain are equal
iff they agree at every input.
"""

# Litex 关键词专栏：`$fn_eq(f,g)`。
#
# `$fn_eq` 的作用是把 pointwise equality 折叠成函数相等。也就是说，先证明
# `forall x domain: f(x)=g(x)`，然后用 `$fn_eq(f,g)` 让 Litex 记录两个函数相等。
# 这个关键词对应 Definition 3.3.7 本体；它不是函数定义语句。

sketch:
    have fn poly1(x R) R = x^2 + 2 * x + 1
    have fn poly2(x R) R = (x + 1)^2

    forall x R:
        poly1(x) = poly2(x)

    $fn_eq(poly1, poly2)

"""
Example 3.3.8. The functions x |-> x^2+2x+1 and x |-> (x+1)^2 are equal on
R. The functions x |-> x and x |-> |x| are equal on the positive axis, but not
on all of R; function equality depends on the chosen domain.
"""

# 这个 example 不是在介绍新关键词，而是在提醒 domain/codomain 是函数数据的一部分。
# 同一个 formula 在较小 domain 上可能相等，在较大 domain 上可能不相等。

sketch:
    have fn id_on_N_pos(x N_pos) R = x
    have fn abs_on_N_pos(x N_pos) R = abs(x)

    forall x N_pos:
        abs_on_N_pos(x) = abs(x) = x = id_on_N_pos(x)

    $fn_eq(id_on_N_pos, abs_on_N_pos)

    have fn id_R(x R) R = x
    have fn abs_R(x R) R = abs(x)

    id_R(-2) = -2
    abs_R(-2) = 2
    id_R(-2) != abs_R(-2)

"""
Example 3.3.9. There is a unique function from the empty set to a fixed target
X. Since the empty set has no inputs, there is no value table to specify.
"""

# empty function 是一个 source-facing example：它说明函数定义仍然需要 domain，
# 即使 domain 没有元素。证明路线是空 domain 上的 vacuous pointwise equality，
# 然后用 `$fn_eq` 折叠成函数相等。

sketch:
    have fn empty_to_N(x {}) N = 0
    have fn empty_to_N_alt(x {}) N = 1

    claim:
        ? forall x {}:
            empty_to_N(x) = empty_to_N_alt(x)
        by contra:
            ? empty_to_N(x) = empty_to_N_alt(x)
            not $is_nonempty_set({})
            witness $is_nonempty_set({}) from x
            impossible $is_nonempty_set({})

    $fn_eq(empty_to_N, empty_to_N_alt)



"""
Definition 3.3.10. Composition is defined by (g o f)(x) := g(f(x)). It is
undefined when the codomain of f does not match the domain of g.
"""

# composition 在 Litex 里最自然就是 nested application；如果要把它当作
# 函数对象，可以用 anonymous function 写出 `'(x X) Z {g(f(x))}`。

"""
Example 3.3.11. For f(n)=2n and g(n)=n+3, g after f differs from f after g.
"""

# 这个 example 的重点是 composition 不交换：同样两个函数，换顺序会给出不同值。

sketch:
    have fn double_nat(n N) N = 2 * n
    have fn add3_nat(n N) N = n + 3
    have fn add3_after_double(n N) N = add3_nat(double_nat(n))
    have fn double_after_add3(n N) N = double_nat(add3_nat(n))

    add3_after_double(1) = add3_nat(double_nat(1)) = add3_nat(2) = 5
    double_after_add3(1) = double_nat(add3_nat(1)) = double_nat(4) = 8
    add3_after_double(1) != double_after_add3(1)

"""
Lemma 3.3.12. Composition is associative: f o (g o h) = (f o g) o h.
"""

# 证明路线是函数外延性：两种加括号方式展开后，对每个 x 都是 `f(g(h(x)))`。

sketch:
    claim:
        ? forall X0, Y0, Z0, W0 set, f fn(z Z0) W0, g fn(y Y0) Z0, h fn(x X0) Y0:
            $fn_eq('(t X0) W0 {f(g(h(t)))}, '(t X0) W0 {'(u Y0) W0 {f(g(u))}(h(t))})
        forall x X0:
            '(t X0) W0 {f(g(h(t)))}(x) = f(g(h(x))) = '(u Y0) W0 {f(g(u))}(h(x)) = '(t X0) W0 {'(u Y0) W0 {f(g(u))}(h(t))}(x)
        $fn_eq('(t X0) W0 {f(g(h(t)))}, '(t X0) W0 {'(u Y0) W0 {f(g(u))}(h(t))})

    claim:
        ? forall X0, Y0, Z0, W0 set, f fn(z Z0) W0, g fn(y Y0) Z0, h fn(x X0) Y0:
            $fn_eq('(t X0) W0 {f(g(h(t)))}, '(t X0) W0 {f('(u X0) Z0 {g(h(u))}(t))})
        forall x X0:
            '(t X0) W0 {f(g(h(t)))}(x) = f(g(h(x))) = f('(u X0) Z0 {g(h(u))}(x)) = '(t X0) W0 {f('(u X0) Z0 {g(h(u))}(t))}(x)
        $fn_eq('(t X0) W0 {f(g(h(t)))}, '(t X0) W0 {f('(u X0) Z0 {g(h(u))}(t))})

"""
Remark 3.3.13. In g o f, the right-hand function f is applied first.
"""

# Litex 的 nested application `g(f(x))` makes this order explicit: inner
# application first, outer application second.



"""
Definition 3.3.14. A function is one-to-one, or injective, when equal outputs
force equal inputs.
"""

# Tao 先说 “different inputs give different outputs”，Litex 更常用等价的
# contrapositive-friendly 形式：`f(x1)=f(x2) => x1=x2`。这就是定义本体。
prop is_injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

"""
Example 3.3.15. The square function Z->Z is not injective, because -1 and 1
have the same square. Restricting the domain to N makes the same formula
injective.
"""

# 这个 example 的核心是 domain dependence。失败的一边用 1 和 -1 作为反例；
# 成功的一边用 `sqrt(x^2)=x` for `x in N` 把平方相等消去。

sketch:
    have fn square_Z(z Z) Z = z^2
    square_Z(1) = 1
    square_Z(-1) = 1
    1 != -1

    by contra:
        ? not $is_injective_fn(Z, Z, square_Z)
        $is_injective_fn(Z, Z, square_Z)
        square_Z(1) = square_Z(-1)
        1 = -1
        impossible 1 = -1

    have fn square_N(n N) Z = n^2

    claim:
        ? $is_injective_fn(N, Z, square_N)
        forall x1, x2 N:
            square_N(x1) = square_N(x2)
            =>:
                x1^2 = square_N(x1) = square_N(x2) = x2^2
                sqrt(x1^2) = sqrt(x2^2)
                x1 = sqrt(x1^2) = sqrt(x2^2) = x2
        $is_injective_fn(N, Z, square_N)

"""
Remark 3.3.16. A non-injective function is two-to-one in the sense that two
distinct inputs can map to the same output.
"""

# This is terminology rather than a new theorem interface; Example 3.3.15 and
# Example 3.3.21 give the concrete witnesses.

"""
Definition 3.3.17. A function is onto, or surjective, when every target value
is hit by some input.
"""

# surjective 的核心关系是：对每个 target-side `y`，存在 source-side `x`
# 使得 `y=f(x)`。
prop is_surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

"""
Example 3.3.18. The square function Z->Z is not onto, because negative
integers are not squares. If the codomain is restricted to the set of square
numbers, the same formula becomes onto.
"""

# 这个 example 的核心是 codomain dependence。先证明 -1 没有 square preimage；
# 然后反证 surjectivity，因为 onto 会给出一个命中 -1 的 input。

sketch:
    have fn square_Z(z Z) Z = z^2

    by contra:
        ? not exist n Z st {square_Z(n) = -1}
        have by exist n Z st {square_Z(n) = -1}: k
        square_Z(k) = k^2
        k^2 = square_Z(k) = -1
        k^2 >= 0
        impossible -1 >= 0

    by contra:
        ? not $is_surjective_fn(Z, Z, square_Z)
        $is_surjective_fn(Z, Z, square_Z)
        exist n Z st {-1 = square_Z(n)}
        have by exist n Z st {-1 = square_Z(n)}: k2
        square_Z(k2) = -1
        square_Z(k2) != -1
        impossible square_Z(k2) = -1

    # With codomain `fn_range(square_Z)`, surjectivity is true by construction.

"""
Remark 3.3.19. Injectivity and surjectivity are dual notions; Tao points to
the exercises for composition and cancellation laws.
"""

# No new local vocabulary is needed here. The definitions above expose the two
# quantifier directions that later exercises use.

"""
Definition 3.3.20. A function is bijective when it is both one-to-one and onto.
"""

# bijective 是 injective 和 surjective 的合取，不是 vertical line test 本身。
prop is_bijective_fn(S, T set, f fn(x S) T):
    $is_injective_fn(S, T, f)
    $is_surjective_fn(S, T, f)

"""
Example 3.3.21. Three finite functions show failure of injectivity, failure of
surjectivity, and bijectivity.
"""

# 这里保留原书的三张有限 value table。`not injective` 用两个同值输入反证；
# `not surjective` 用缺失的 4 反证；bijection 用有限枚举和显式 witnesses。

sketch:
    have fn finite_not_injective(x {0, 1, 2}) {3, 4} by cases:
        case x = 0: 3
        case x = 1: 3
        case x = 2: 4

    finite_not_injective(0) = 3
    finite_not_injective(1) = 3
    0 != 1
    by contra:
        ? not $is_injective_fn({0, 1, 2}, {3, 4}, finite_not_injective)
        $is_injective_fn({0, 1, 2}, {3, 4}, finite_not_injective)
        finite_not_injective(0) = finite_not_injective(1)
        0 = 1
        impossible 0 = 1

    have fn finite_not_surjective(x {0, 1}) {2, 3, 4} by cases:
        case x = 0: 2
        case x = 1: 3

    finite_not_surjective(0) = 2
    finite_not_surjective(1) = 3
    not 4 $in {2, 3}
    by contra:
        ? not $is_surjective_fn({0, 1}, {2, 3, 4}, finite_not_surjective)
        $is_surjective_fn({0, 1}, {2, 3, 4}, finite_not_surjective)
        exist x {0, 1} st {4 = finite_not_surjective(x)}
        have by exist x {0, 1} st {4 = finite_not_surjective(x)}: a
        a = 0 or a = 1
        by cases:
            ? finite_not_surjective(a) $in {2, 3}
            case a = 0:
                finite_not_surjective(a) = finite_not_surjective(0) = 2
                finite_not_surjective(a) $in {2, 3}
            case a = 1:
                finite_not_surjective(a) = finite_not_surjective(1) = 3
                finite_not_surjective(a) $in {2, 3}
        4 = finite_not_surjective(a)
        4 $in {2, 3}
        impossible 4 $in {2, 3}

    have fn finite_bijection(x {0, 1, 2}) {3, 4, 5} by cases:
        case x = 0: 3
        case x = 1: 4
        case x = 2: 5

    finite_bijection(0) = 3
    finite_bijection(1) = 4
    finite_bijection(2) = 5

    claim:
        ? $is_injective_fn({0, 1, 2}, {3, 4, 5}, finite_bijection)
        by enumerate finite_set:
            ? forall x1, x2 {0, 1, 2}:
                finite_bijection(x1) = finite_bijection(x2)
                =>:
                    x1 = x2
        $is_injective_fn({0, 1, 2}, {3, 4, 5}, finite_bijection)

    claim:
        ? $is_surjective_fn({0, 1, 2}, {3, 4, 5}, finite_bijection)
        by cases:
            ? forall y {3, 4, 5}:
                exist x {0, 1, 2} st {y = finite_bijection(x)}
            case y = 3:
                witness exist x {0, 1, 2} st {y = finite_bijection(x)} from 0:
                    finite_bijection(0) = 3
                    y = 3
                    y = finite_bijection(0)
            case y = 4:
                witness exist x {0, 1, 2} st {y = finite_bijection(x)} from 1:
                    finite_bijection(1) = 4
                    y = 4
                    y = finite_bijection(1)
            case y = 5:
                witness exist x {0, 1, 2} st {y = finite_bijection(x)} from 2:
                    finite_bijection(2) = 5
                    y = 5
                    y = finite_bijection(2)
        $is_surjective_fn({0, 1, 2}, {3, 4, 5}, finite_bijection)

    $is_bijective_fn({0, 1, 2}, {3, 4, 5}, finite_bijection)

"""
Example 3.3.22. The successor formula is a bijection N->N_pos, but the same
formula is not a bijection N->N because 0 is not hit.
"""

# successor 作为 `N -> N_pos` 是 bijection；同样的 `n+1` 如果看成 `N -> N`
# 就不是 onto，因为 0 没有 preimage。这正是 Tao 反复强调的 domain/range 依赖。

sketch:
    have fn succ(n N) N_pos = n + 1

    claim:
        ? $is_injective_fn(N, N_pos, succ)
        forall x1, x2 N:
            succ(x1) = succ(x2)
            =>:
                x1 = (x1 + 1) - 1 = succ(x1) - 1 = succ(x2) - 1 = (x2 + 1) - 1 = x2

    claim:
        ? $is_surjective_fn(N, N_pos, succ)
        claim:
            ? forall y N_pos:
                exist x N st {y = succ(x)}
            y - 1 $in N
            witness exist x N st {y = succ(x)} from y - 1:
                succ(y - 1) = (y - 1) + 1
                (y - 1) + 1 = y
                y = succ(y - 1)
        $is_surjective_fn(N, N_pos, succ)

    $is_bijective_fn(N, N_pos, succ)

    have fn succ_to_N(n N) N = n + 1

    0 $in N
    not 0 $in N_pos

    by contra:
        ? not exist x N st {succ_to_N(x) = 0}
        have by exist x N st {succ_to_N(x) = 0}: k
        succ_to_N(k) = k + 1
        0 = succ_to_N(k) = k + 1
        k + 1 $in N_pos
        0 $in N_pos
        impossible 0 $in N_pos

    by contra:
        ? not $is_surjective_fn(N, N, succ_to_N)
        $is_surjective_fn(N, N, succ_to_N)
        exist x N st {0 = succ_to_N(x)}
        have by exist x N st {0 = succ_to_N(x)}: k2
        succ_to_N(k2) = 0
        succ_to_N(k2) != 0
        impossible succ_to_N(k2) = 0

"""
Remark 3.3.23. A bijection can be viewed as a one-to-one correspondence or
perfect matching between the domain and codomain.
"""

# This is notation and terminology: the finite bijection in Example 3.3.21 is
# the correspondence 0<->3, 1<->4, 2<->5.

"""
Remark 3.3.24 and Exercise 3.3.6. Bijective does not mean merely that each
input has a unique output; that is just being a function. For a bijection,
each y in Y has a unique preimage x in X, defining f^{-1}:Y->X, and the two
cancellation laws hold.
"""

# Litex 中的反函数最好写成一个 template：给定 X、Y 和一个 bijection f，
# `have fn ... as set` 用“每个 y 有唯一 preimage”生成函数。这里不要求
# nonempty_set，因为空集到空集的 bijection 也应该有反函数。
template<X set, Y set, f fn(x X) Y: $is_bijective_fn(X, Y, f)>:
    have fn inverse_of_bijection as set:
        ? forall y Y:
            exist! x X st {y = f(x)}
        $is_injective_fn(X, Y, f)
        $is_surjective_fn(X, Y, f)
        exist x X st {y = f(x)}
        forall x1, x2 X:
            y = f(x1)
            y = f(x2)
            =>:
                f(x1) = y
                f(x2) = y
                f(x1) = f(x2)
                x1 = x2
        exist! x X st {y = f(x)}

claim:
    ? forall X, Y set, f fn(x X) Y, x X:
        $is_bijective_fn(X, Y, f)
        =>:
            \inverse_of_bijection<X, Y, f>(f(x)) = x
    x = \inverse_of_bijection<X, Y, f>(f(x))
    \inverse_of_bijection<X, Y, f>(f(x)) = x

claim:
    ? forall X, Y set, f fn(x X) Y, y Y:
        $is_bijective_fn(X, Y, f)
        =>:
            f(\inverse_of_bijection<X, Y, f>(y)) = y
    y = f(\inverse_of_bijection<X, Y, f>(y))
    f(\inverse_of_bijection<X, Y, f>(y)) = y

# Remaining follow-up: the checked inverse template above covers Remark 3.3.24
# and Exercise 3.3.6.  A polished reusable package should still add standard
# notation for inverse functions and the composition laws from Exercise 3.3.7.


# Analysis I, Chapter 3, Section 3.4: Images and inverse images.
#
# 样章分节：这一节展示函数如何把 subset 推到 forward image，或者把 target
# subset 拉回 inverse image。Tao 的 replacement、power set、family union
# 公理继续保留 source-facing 说明；Litex 主线用 builtin set/function surface。


# Section 3.4 uses the injective/surjective/bijective vocabulary introduced in
# Section 3.3 above; the split-file duplicate definition is removed here.

"""
Full range of a function.  `function_range<X,Y,f>` is the subset of Y whose
elements are exactly the values f(x) with x in X.
"""

# Membership predicate for the full range: y is in the range of f exactly when
# y has a preimage in the source X.
prop has_preimage(X, Y set, f fn(z X) Y, y Y):
    exist x X st {y = f(x)}

template<X set, Y set, f fn(x X) Y>:
    have function_range set = {y Y: $has_preimage(X, Y, f, y)}

"""
Restricted image of a subset.  `restricted_image<X,Y,f,A>` is the set
f(A) = {f(x) : x in A}, viewed as a subset of Y.
"""

# Membership predicate for the restricted image: y is in f(A) exactly when y
# has a preimage in A.  Since A is a subset of X, the witness is also recorded
# as an element of X.
prop has_preimage_in_subset(X, Y set, A power_set(X), f fn(z X) Y, y Y):
    exist x A st {x $in X, y = f(x)}

template<X set, Y set, f fn(x X) Y, A power_set(X)>:
    have restricted_image set = {y Y: $has_preimage_in_subset(X, Y, A, f, y)}

"""
Inverse of an injective map on its image.  If f:X->Y is injective, then every
point in the range of f has a unique preimage in X.  The template packages
that unique-preimage rule as a function from the range of f back to X.
"""

# This is the Section 3.4 analogue of the inverse function from Section 3.3:
# no surjectivity onto Y is assumed; the codomain is restricted to the image.
template<X set, Y set, f fn(x X) Y: $is_injective_fn(X, Y, f)>:
    have fn inverse_function as set:
        ? forall y \function_range<X, Y, f>:
            exist! x X st {y = f(x)}
        y $in \function_range<X, Y, f>
        $has_preimage(X, Y, f, y)
        exist x X st {y = f(x)}
        forall x1, x2 X:
            y = f(x1)
            y = f(x2)
            =>:
                f(x1) = y
                f(x2) = y
                f(x1) = f(x2)
                x1 = x2
        exist! x X st {y = f(x)}

# Evaluation law for the image-level inverse: applying f and then the inverse
# returns the original source point.
claim:
    ? forall X, Y set, f fn(x X) Y, x X:
        $is_injective_fn(X, Y, f)
        =>:
            f(x) $in \function_range<X, Y, f>
            \inverse_function<X, Y, f>(f(x)) = x
    witness exist u X st {f(x) = f(u)} from x:
        f(x) = f(x)
    $has_preimage(X, Y, f, f(x))
    f(x) $in {y Y: $has_preimage(X, Y, f, y)}
    f(x) $in \function_range<X, Y, f>
    x = \inverse_function<X, Y, f>(f(x))
    \inverse_function<X, Y, f>(f(x)) = x

"""
Definition 3.4.1. The forward image f(A) consists exactly of values f(x) with
x in A.
"""

# `B` 是 `A` 在 f 下的 image：A 里每个点都被送进 B，B 里每个点也都来自
# A 中某个 preimage。这比只写 `forall x A: f(x) in B` 更精确。
prop is_forward_image_of(S, T set, f fn(x S) T, A, B set):
    A $subset S
    B $subset T
    forall x A:
        f(x) $in B
    forall y B:
        exist x A st {y = f(x)}


"""
Example 3.4.2. If f:N->N is f(x)=2x, then the forward image of {1,2,3} is
{2,4,6}.
"""

# 有限 doubling example 很适合写成 Litex：集合是具体的，preimage witness
# 可以枚举。`double_on_three` 是全局函数 `double_nat` 限制到 `{1,2,3}`
# 后的 finite-domain version；先展开 section vocabulary `is_forward_image_of`，
# 再给出 builtin surface `fn_range_on(double_on_three,{1,2,3}) = {2,4,6}`。

sketch:
    have fn double_nat(n N) N = 2 * n
    have fn double_on_three(n {1, 2, 3}) {2, 4, 6} by cases:
        case n = 1: 2
        case n = 2: 4
        case n = 3: 6

    by enumerate finite_set:
        ? forall x {1, 2, 3}:
            x $in N

    {1, 2, 3} $subset N

    by enumerate finite_set:
        ? forall y {2, 4, 6}:
            y $in N

    {2, 4, 6} $subset N

    claim:
        ? $is_forward_image_of({1, 2, 3}, {2, 4, 6}, double_on_three, {1, 2, 3}, {2, 4, 6})
        {1, 2, 3} $subset {1, 2, 3}
        {2, 4, 6} $subset {2, 4, 6}
        by enumerate finite_set:
            ? forall x {1, 2, 3}:
                double_on_three(x) $in {2, 4, 6}
        by enumerate finite_set:
            ? forall y {2, 4, 6}:
                exist x {1, 2, 3} st {y = double_on_three(x)}
            by cases:
                ? exist x {1, 2, 3} st {y = double_on_three(x)}
                case y = 2:
                    witness exist x {1, 2, 3} st {y = double_on_three(x)} from 1:
                        y = 2
                        double_on_three(1) = 2
                case y = 4:
                    witness exist x {1, 2, 3} st {y = double_on_three(x)} from 2:
                        y = 4
                        double_on_three(2) = 4
                case y = 6:
                    witness exist x {1, 2, 3} st {y = double_on_three(x)} from 3:
                        y = 6
                        double_on_three(3) = 6
        $is_forward_image_of({1, 2, 3}, {2, 4, 6}, double_on_three, {1, 2, 3}, {2, 4, 6})

    witness exist x {1, 2, 3} st {x $in N, double_nat(1) = double_nat(x)} from 1:
        1 $in N
        double_nat(1) = double_nat(1)
    $has_preimage_in_subset(N, N, {1, 2, 3}, double_nat, double_nat(1))
    double_nat(1) $in {y N: $has_preimage_in_subset(N, N, {1, 2, 3}, double_nat, y)}
    double_nat(1) $in \restricted_image<N, N, double_nat, {1, 2, 3}>

    # Builtin alternative: outside this source-facing reconstruction, the
    # restricted image can be written directly with `fn_range_on`.
    double_on_three(1) $in fn_range_on(double_on_three, {1, 2, 3})
    double_on_three(2) $in fn_range_on(double_on_three, {1, 2, 3})
    double_on_three(3) $in fn_range_on(double_on_three, {1, 2, 3})

    claim:
        ? forall y fn_range_on(double_on_three, {1, 2, 3}):
            y $in {2, 4, 6}
        y $in fn_range_on(double_on_three, {1, 2, 3})
        have by preimage k from y $in fn_range_on(double_on_three, {1, 2, 3})
        k $in {1, 2, 3}
        double_on_three(k) $in {2, 4, 6}
        y = double_on_three(k)
        y $in {2, 4, 6}

    fn_range_on(double_on_three, {1, 2, 3}) $subset {2, 4, 6}

    claim:
        ? forall y {2, 4, 6}:
            y $in fn_range_on(double_on_three, {1, 2, 3})
        by cases:
            ? y $in fn_range_on(double_on_three, {1, 2, 3})
            case y = 2:
                double_on_three(1) = 2
                y = double_on_three(1)
                y $in fn_range_on(double_on_three, {1, 2, 3})
            case y = 4:
                double_on_three(2) = 4
                y = double_on_three(2)
                y $in fn_range_on(double_on_three, {1, 2, 3})
            case y = 6:
                double_on_three(3) = 6
                y = double_on_three(3)
                y $in fn_range_on(double_on_three, {1, 2, 3})

    {2, 4, 6} $subset fn_range_on(double_on_three, {1, 2, 3})

    by extension:
        ? fn_range_on(double_on_three, {1, 2, 3}) = {2, 4, 6}

    count(fn_range_on(double_on_three, {1, 2, 3})) = count({2, 4, 6}) = 3

    have by preimage builtin_k from double_on_three(1) $in fn_range_on(double_on_three, {1, 2, 3})
    builtin_k $in {1, 2, 3}

"""
Example 3.4.3. If f:Z->Z is f(x)=x^2, then the forward image of
{-1,0,1,2} is {0,1,4}.
"""

# Tao marks this example informal because Z is introduced in the next section.
# Litex already has builtin integers, so the same finite image can be checked
# here.  The image is smaller because -1 and 1 have the same square.

sketch:
    have fn square_Z(z Z) Z = z^2
    have fn square_on_example(z {-1, 0, 1, 2}) {0, 1, 4} by cases:
        case z = -1: 1
        case z = 0: 0
        case z = 1: 1
        case z = 2: 4

    by enumerate finite_set:
        ? forall z {-1, 0, 1, 2}:
            z $in Z

    {-1, 0, 1, 2} $subset Z

    by enumerate finite_set:
        ? forall y {0, 1, 4}:
            y $in Z

    {0, 1, 4} $subset Z

    claim:
        ? $is_forward_image_of({-1, 0, 1, 2}, {0, 1, 4}, square_on_example, {-1, 0, 1, 2}, {0, 1, 4})
        {-1, 0, 1, 2} $subset {-1, 0, 1, 2}
        {0, 1, 4} $subset {0, 1, 4}
        by enumerate finite_set:
            ? forall z {-1, 0, 1, 2}:
                square_on_example(z) $in {0, 1, 4}
        by enumerate finite_set:
            ? forall y {0, 1, 4}:
                exist z {-1, 0, 1, 2} st {y = square_on_example(z)}
            by cases:
                ? exist z {-1, 0, 1, 2} st {y = square_on_example(z)}
                case y = 0:
                    witness exist z {-1, 0, 1, 2} st {y = square_on_example(z)} from 0:
                        y = 0
                        square_on_example(0) = 0
                case y = 1:
                    witness exist z {-1, 0, 1, 2} st {y = square_on_example(z)} from -1:
                        y = 1
                        square_on_example(-1) = 1
                case y = 4:
                    witness exist z {-1, 0, 1, 2} st {y = square_on_example(z)} from 2:
                        y = 4
                        square_on_example(2) = 4
        $is_forward_image_of({-1, 0, 1, 2}, {0, 1, 4}, square_on_example, {-1, 0, 1, 2}, {0, 1, 4})

    square_on_example(-1) $in fn_range_on(square_on_example, {-1, 0, 1, 2})
    square_on_example(0) $in fn_range_on(square_on_example, {-1, 0, 1, 2})
    square_on_example(1) $in fn_range_on(square_on_example, {-1, 0, 1, 2})
    square_on_example(2) $in fn_range_on(square_on_example, {-1, 0, 1, 2})

    claim:
        ? forall y fn_range_on(square_on_example, {-1, 0, 1, 2}):
            y $in {0, 1, 4}
        y $in fn_range_on(square_on_example, {-1, 0, 1, 2})
        have by preimage z from y $in fn_range_on(square_on_example, {-1, 0, 1, 2})
        z $in {-1, 0, 1, 2}
        square_on_example(z) $in {0, 1, 4}
        y = square_on_example(z)
        y $in {0, 1, 4}

    fn_range_on(square_on_example, {-1, 0, 1, 2}) $subset {0, 1, 4}

    claim:
        ? forall y {0, 1, 4}:
            y $in fn_range_on(square_on_example, {-1, 0, 1, 2})
        by cases:
            ? y $in fn_range_on(square_on_example, {-1, 0, 1, 2})
            case y = 0:
                square_on_example(0) = 0
                y = square_on_example(0)
                y $in fn_range_on(square_on_example, {-1, 0, 1, 2})
            case y = 1:
                square_on_example(-1) = 1
                y = square_on_example(-1)
                y $in fn_range_on(square_on_example, {-1, 0, 1, 2})
            case y = 4:
                square_on_example(2) = 4
                y = square_on_example(2)
                y $in fn_range_on(square_on_example, {-1, 0, 1, 2})

    {0, 1, 4} $subset fn_range_on(square_on_example, {-1, 0, 1, 2})

    by extension:
        ? fn_range_on(square_on_example, {-1, 0, 1, 2}) = {0, 1, 4}

    count(fn_range_on(square_on_example, {-1, 0, 1, 2})) = count({0, 1, 4}) = 3
    count({-1, 0, 1, 2}) = 4
    square_Z(-1) = 1
    square_Z(1) = 1
    -1 != 1
    square_Z(-2) = 4
    square_on_example(2) = 4
    square_on_example(2) $in fn_range_on(square_on_example, {-1, 0, 1, 2})
    4 = square_on_example(2)
    4 $in fn_range_on(square_on_example, {-1, 0, 1, 2})
    not -2 $in {-1, 0, 1, 2}

"""
Definition 3.4.4. The inverse image f^{-1}(U) consists of inputs whose values
land in U.
"""

# inverse image 不要求 f 可逆。它只是把 target-side subset U 拉回到 source：
# `x in A` 等价于 `f(x) in U`。
prop is_inverse_image_of(S, T set, f fn(x S) T, U, A set):
    U $subset T
    A $subset S
    forall x A:
        f(x) $in U
    forall x S:
        f(x) $in U
        =>:
            x $in A

"""
Example 3.4.5. For f:N->N, f(x)=2x, the forward image of {1,2,3}
is {2,4,6}, while the inverse image of {1,2,3} is just {1}.
"""

# This is the first concrete warning that forward image and inverse image are
# different operations.  The input set `{1,2,3}` maps forward to `{2,4,6}`,
# but pulling `{1,2,3}` back through the same doubling map gives only `{1}`.

sketch:
    have fn double_nat(n N) N = 2 * n
    have fn double_on_one(n {1}) {2} by cases:
        case n = 1: 2

    double_nat(1) = 2
    2 $in {1, 2, 3}
    double_nat(2) = 4
    not 4 $in {1, 2, 3}

    claim:
        ? $is_inverse_image_of(N, N, double_nat, {1, 2, 3}, {1})
        by enumerate finite_set:
            ? forall u {1, 2, 3}:
                u $in N
        {1, 2, 3} $subset N
        by enumerate finite_set:
            ? forall a {1}:
                a $in N
        {1} $subset N
        by enumerate finite_set:
            ? forall x {1}:
                double_nat(x) $in {1, 2, 3}
        claim:
            ? forall x N:
                double_nat(x) $in {1, 2, 3}
                =>:
                    x $in {1}
            double_nat(x) = 1 or double_nat(x) = 2 or double_nat(x) = 3
            by cases:
                ? x $in {1}
                case double_nat(x) = 1:
                    double_nat(x) = 2 * x
                    2 * x = 1
                    x = 1 / 2
                    x $in N
                    not 1 / 2 $in N
                    impossible not 1 / 2 $in N
                case double_nat(x) = 2:
                    double_nat(x) = 2 * x
                    2 * x = 2
                    x = 1
                    x $in {1}
                case double_nat(x) = 3:
                    double_nat(x) = 2 * x
                    2 * x = 3
                    x = 3 / 2
                    x $in N
                    not 3 / 2 $in N
                    impossible not 3 / 2 $in N
        $is_inverse_image_of(N, N, double_nat, {1, 2, 3}, {1})

    # Applying f again to this inverse image gives `{2}`, not `{1,2,3}`.
    double_on_one(1) = 2
    count({2}) = 1
    count({1, 2, 3}) = 3
    claim:
        ? {2} != {1, 2, 3}
        by contra:
            ? {2} != {1, 2, 3}
            {2} = {1, 2, 3}
            count({2}) = count({1, 2, 3})
            1 = count({2}) = count({1, 2, 3}) = 3
            impossible 1 = 3

"""
Example 3.4.6. For f:Z->Z, f(x)=x^2, the inverse image of {0,1,4}
is {-2,-1,0,1,2}.  This inverse image makes sense even though f is not
invertible.
"""

# The calculation is ordinary finite preimage reasoning.  The only deferred
# fact is the elementary integer-square classification for roots of 1 and 4.

sketch:
    have fn square_Z(z Z) Z = z^2

    square_Z(-1) = 1
    square_Z(1) = 1
    -1 != 1

    by enumerate finite_set:
        ? forall u {0, 1, 4}:
            u $in Z
    {0, 1, 4} $subset Z

    by enumerate finite_set:
        ? forall z {-2, -1, 0, 1, 2}:
            z $in Z
    {-2, -1, 0, 1, 2} $subset Z

    claim:
        ? forall z Z:
            square_Z(z) $in {0, 1, 4}
            =>:
                z $in {-2, -1, 0, 1, 2}
        square_Z(z) = 0 or square_Z(z) = 1 or square_Z(z) = 4
        square_Z(z) = z^2
        by cases:
            ? z $in {-2, -1, 0, 1, 2}
            case square_Z(z) = 0:
                z^2 = square_Z(z) = 0
                z = 0
                z $in {-2, -1, 0, 1, 2}
            case square_Z(z) = 1:
                z^2 = square_Z(z) = 1
                (z - 1) * (z + 1) = z^2 - 1 = 0
                z - 1 = 0 or z + 1 = 0
                by cases:
                    ? z $in {-2, -1, 0, 1, 2}
                    case z - 1 = 0:
                        z = 1
                        z $in {-2, -1, 0, 1, 2}
                    case z + 1 = 0:
                        z = -1
                        z $in {-2, -1, 0, 1, 2}
            case square_Z(z) = 4:
                z^2 = square_Z(z) = 4
                (z - 2) * (z + 2) = z^2 - 4 = 0
                z - 2 = 0 or z + 2 = 0
                by cases:
                    ? z $in {-2, -1, 0, 1, 2}
                    case z - 2 = 0:
                        z = 2
                        z $in {-2, -1, 0, 1, 2}
                    case z + 2 = 0:
                        z = -2
                        z $in {-2, -1, 0, 1, 2}

    claim:
        ? $is_inverse_image_of(Z, Z, square_Z, {0, 1, 4}, {-2, -1, 0, 1, 2})
        {0, 1, 4} $subset Z
        {-2, -1, 0, 1, 2} $subset Z
        by enumerate finite_set:
            ? forall z {-2, -1, 0, 1, 2}:
                square_Z(z) $in {0, 1, 4}
        forall z Z:
            square_Z(z) $in {0, 1, 4}
            =>:
                z $in {-2, -1, 0, 1, 2}
        $is_inverse_image_of(Z, Z, square_Z, {0, 1, 4}, {-2, -1, 0, 1, 2})

    # Since `f({-1,0,1,2}) = {0,1,4}`, the inverse image found above contains
    # -2, which was not in the original set.
    -2 $in {-2, -1, 0, 1, 2}
    not -2 $in {-1, 0, 1, 2}

"""
Remark 3.4.7. For a bijection, inverse-function notation and inverse-image
notation are compatible.
"""

# The checked statement records the image-restricted version behind this
# remark: if f is injective and B is the forward image of A, then pulling B
# back gives exactly A.  A bijection is the special case where the image is the
# whole target.

sketch:
    claim:
        ? forall S, T set, f fn(x S) T, A, B set:
            A $subset S
            $is_injective_fn(S, T, f)
            $is_forward_image_of(S, T, f, A, B)
            =>:
                $is_inverse_image_of(S, T, f, B, A)
        A $subset S
        B $subset T
        claim:
            ? forall x A:
                f(x) $in B
            f(x) $in B
        claim:
            ? forall x S:
                f(x) $in B
                =>:
                    x $in A
            A $subset S
            claim:
                ? forall a A:
                    a $in S
                a $in S
            claim:
                ? forall a A:
                    f(a) $in T
                a $in S
                f(a) $in T
            have by exist a A st {f(x) = f(a)}: a
            a $in S
            f(x) = f(a)
            f(a) = f(x)
            x = a
            x $in A
        $is_inverse_image_of(S, T, f, B, A)



"""
Axiom 3.10. Y^X is the set of all functions from X to Y.
"""

# In Litex, Tao's function-space notation `Y^X` is written as `fn(x X) Y`:
# an object of this type takes an input `x` in `X` and returns a value in `Y`.

sketch:
    have X, Y set

    have f fn(x X) Y

"""
Example 3.4.8. For X={4,7} and Y={0,1}, there are four functions X -> Y.
"""

# Each function chooses independently where 4 and 7 go.  Thus the function
# space has the four concrete maps 00, 01, 10, and 11. Proposition 3.6.14(f)
# later explains the general count `count(Y^X) = count(Y)^count(X)`.

sketch:
    have fn bit_00(x {4, 7}) {0, 1} by cases:
        case x = 4: 0
        case x = 7: 0

    have fn bit_01(x {4, 7}) {0, 1} by cases:
        case x = 4: 0
        case x = 7: 1

    have fn bit_10(x {4, 7}) {0, 1} by cases:
        case x = 4: 1
        case x = 7: 0

    have fn bit_11(x {4, 7}) {0, 1} by cases:
        case x = 4: 1
        case x = 7: 1

    bit_00 $in fn(x {4, 7}) {0, 1}
    bit_01 $in fn(x {4, 7}) {0, 1}
    bit_10 $in fn(x {4, 7}) {0, 1}
    bit_11 $in fn(x {4, 7}) {0, 1}

    bit_00(4) = 0
    bit_00(7) = 0
    bit_01(4) = 0
    bit_01(7) = 1
    bit_10(4) = 1
    bit_10(7) = 0
    bit_11(4) = 1
    bit_11(7) = 1

"""
Lemma 3.4.9. The collection of all subsets of X is the power set 2^X.
"""

# Litex has `power_set(X)` as the source-facing surface.  The basic membership
# direction is that `U $in power_set(X)` gives `U $subset X`.

sketch:
    forall X set, U set:
        U $in power_set(X)
        =>:
            U $subset X
"""
Remark 3.4.10. For a finite set X, the power set 2^X has 2^{count(X)}
elements; in particular a three-element set has eight subsets.
"""

# The sketch lists the concrete subsets and uses the finite powerset
# cardinality interface for the source count claim.

sketch:
    {} $in power_set({1, 2, 3})
    {1} $in power_set({1, 2, 3})
    {2} $in power_set({1, 2, 3})
    {3} $in power_set({1, 2, 3})
    {1, 2} $in power_set({1, 2, 3})
    {1, 3} $in power_set({1, 2, 3})
    {2, 3} $in power_set({1, 2, 3})
    {1, 2, 3} $in power_set({1, 2, 3})

    {} $in power_set({4, 7})
    {4} $in power_set({4, 7})
    {7} $in power_set({4, 7})
    {4, 7} $in power_set({4, 7})

    $is_finite_set(power_set({1, 2, 3}))
    count(power_set({1, 2, 3})) = 2^count({1, 2, 3})
    count({1, 2, 3}) = 3
    2^count({1, 2, 3}) = 2^3 = 8
    count(power_set({1, 2, 3})) = 8



"""
Axiom 3.11. The union of a set of sets contains exactly the elements of the
member sets.
"""

# In Litex this family union is written with `cup(F)`, where `F` is a set whose
# elements are themselves sets.
# The builtin membership rule proves `x $in cup(F)` from `A $in F` and
# `x $in A`, or from the existential criterion `exist A F st {x $in A}`.
# Conversely, storing `x $in cup(F)` releases `exist A F st {x $in A}`.

"""
Indexed family unions.  If I is an index set and each i in I labels a set A_i
inside a common universe Y, then the union over i in I contains exactly the
objects that lie in at least one A_i.
"""

# This is Tao's unnumbered bridge from replacement plus union to indexed
# notation.  The family is a function `A fn(i I) power_set(Y)`, and the indexed
# union is the subset of Y whose members have some index witness.
prop is_in_indexed_union(I set, Y set, A fn(i I) power_set(Y), z Y):
    exist i I st {z $in A(i)}

template<I set, Y set, A fn(i I) power_set(Y)>:
    have indexed_union set = {z Y: $is_in_indexed_union(I, Y, A, z)}

# Proof debt / source construction.  Tao obtains indexed unions by first using
# replacement to form `{A_i : i in I}` and then taking `cup`.  The template
# above is the checked chapter-facing notation; the replacement-plus-cup
# equality and empty-index convention remain reusable set-theory interfaces.
sketch:
    have fn A(i {1, 2, 3}) power_set(N) by cases:
        case i = 1: {2, 3}
        case i = 2: {3, 4}
        case i = 3: {4, 5}

    A(1) = {2, 3}
    A(2) = {3, 4}
    A(3) = {4, 5}
    {2, 3} $subset A(1)
    2 $in {2, 3}
    2 $in A(1)
    witness exist i {1, 2, 3} st {2 $in A(i)} from 1:
        2 $in A(1)
    $is_in_indexed_union({1, 2, 3}, N, A, 2)
    2 $in {z N: $is_in_indexed_union({1, 2, 3}, N, A, z)}
    2 $in \indexed_union<{1, 2, 3}, N, A>

"""
Indexed family intersections.  If I is non-empty and each i in I labels a set
A_i inside a common universe Y, then the intersection over i in I contains
exactly the objects that lie in every A_i.
"""

# Tao chooses a base index beta to get an ambient set for specification.  In
# Litex we pass an ambient universe Y explicitly and still keep I non-empty,
# matching the source theorem's requirement.
prop is_in_indexed_intersection(I nonempty_set, Y set, A fn(i I) power_set(Y), z Y):
    forall i I:
        z $in A(i)

template<I nonempty_set, Y set, A fn(i I) power_set(Y)>:
    have indexed_intersection set = {z Y: $is_in_indexed_intersection(I, Y, A, z)}

# Proof debt / source construction.  Tao chooses a base index beta to make the
# intersection a bounded specification subset.  The explicit ambient set `Y`
# makes the checked Litex route simpler; beta-independence of the source
# construction is still a theorem-package interface, not proved here.
sketch:
    have fn A(i {1, 2, 3}) power_set(N) by cases:
        case i = 1: {2, 3}
        case i = 2: {3, 4}
        case i = 3: {3, 5}

    A(1) = {2, 3}
    A(2) = {3, 4}
    A(3) = {3, 5}
    {2, 3} $subset A(1)
    {3, 4} $subset A(2)
    {3, 5} $subset A(3)
    3 $in A(1)
    3 $in A(2)
    3 $in A(3)
    claim:
        ? forall i {1, 2, 3}:
            3 $in A(i)
        by enumerate finite_set:
            ? forall j {1, 2, 3}:
                3 $in A(j)
    $is_in_indexed_intersection({1, 2, 3}, N, A, 3)
    3 $in {z N: $is_in_indexed_intersection({1, 2, 3}, N, A, z)}
    3 $in \indexed_intersection<{1, 2, 3}, N, A>

"""
Example 3.4.11. The union of {{2,3},{3,4},{4,5}} is {2,3,4,5}.
"""

# The membership rule is: if `A $in F` and `x $in A`, then `x $in cup(F)`.

sketch:
    claim:
        ? {2, 3} != {3, 4}
        by contra:
            ? {2, 3} != {3, 4}
            {2, 3} = {3, 4}
            2 $in {2, 3}
            2 $in {3, 4}
            not 2 $in {3, 4}
            impossible not 2 $in {3, 4}
    claim:
        ? {2, 3} != {4, 5}
        by contra:
            ? {2, 3} != {4, 5}
            {2, 3} = {4, 5}
            2 $in {2, 3}
            2 $in {4, 5}
            not 2 $in {4, 5}
            impossible not 2 $in {4, 5}
    claim:
        ? {3, 4} != {4, 5}
        by contra:
            ? {3, 4} != {4, 5}
            {3, 4} = {4, 5}
            3 $in {3, 4}
            3 $in {4, 5}
            not 3 $in {4, 5}
            impossible not 3 $in {4, 5}

    2 $in {2, 3}
    {2, 3} $in {{2, 3}, {3, 4}, {4, 5}}
    2 $in cup({{2, 3}, {3, 4}, {4, 5}})

    3 $in {2, 3}
    {2, 3} $in {{2, 3}, {3, 4}, {4, 5}}
    3 $in cup({{2, 3}, {3, 4}, {4, 5}})

    4 $in {3, 4}
    {3, 4} $in {{2, 3}, {3, 4}, {4, 5}}
    4 $in cup({{2, 3}, {3, 4}, {4, 5}})

    5 $in {4, 5}
    {4, 5} $in {{2, 3}, {3, 4}, {4, 5}}
    5 $in cup({{2, 3}, {3, 4}, {4, 5}})

    by enumerate finite_set:
        ? forall t {2, 3}:
            t $in {2, 3, 4, 5}
    {2, 3} $subset {2, 3, 4, 5}
    by enumerate finite_set:
        ? forall t {3, 4}:
            t $in {2, 3, 4, 5}
    {3, 4} $subset {2, 3, 4, 5}
    by enumerate finite_set:
        ? forall t {4, 5}:
            t $in {2, 3, 4, 5}
    {4, 5} $subset {2, 3, 4, 5}

    by extension cup({{2, 3}, {3, 4}, {4, 5}}) = {2, 3, 4, 5}:
        claim:
            ? forall x cup({{2, 3}, {3, 4}, {4, 5}}):
                x $in {2, 3, 4, 5}
            x $in cup({{2, 3}, {3, 4}, {4, 5}})
            exist A {{2, 3}, {3, 4}, {4, 5}} st {x $in A}
            have by exist A {{2, 3}, {3, 4}, {4, 5}} st {x $in A}: A
            A = {2, 3} or A = {3, 4} or A = {4, 5}
            by cases:
                ? x $in {2, 3, 4, 5}
                case A = {2, 3}:
                    A $subset {2, 3}
                    x $in {2, 3}
                    {2, 3} $subset {2, 3, 4, 5}
                    x $in {2, 3, 4, 5}
                case A = {3, 4}:
                    A $subset {3, 4}
                    x $in {3, 4}
                    {3, 4} $subset {2, 3, 4, 5}
                    x $in {2, 3, 4, 5}
                case A = {4, 5}:
                    A $subset {4, 5}
                    x $in {4, 5}
                    {4, 5} $subset {2, 3, 4, 5}
                    x $in {2, 3, 4, 5}
        by enumerate finite_set:
            ? forall y {2, 3, 4, 5}:
                y $in cup({{2, 3}, {3, 4}, {4, 5}})

    cup({{2, 3}, {3, 4}, {4, 5}}) = {2, 3, 4, 5}

"""
Remark 3.4.12. The axioms in this section, except unrestricted comprehension,
are the Zermelo-Fraenkel set-theory package.
"""

# Section 3.4 summary: Tao's set-theory axioms and their Litex surfaces.
#
# - Axiom 3.1, sets are objects:
#   `A set` is already an object-level binding in Litex. No Tao-specific
#   wrapper is needed.
# - Axiom 3.2, empty set:
#   the object is `{}`; empty-set membership and non-membership are builtin
#   set facts.
# - Axiom 3.3, singleton and pair sets:
#   displayed finite-set objects such as `{a}` and `{a, b}` are the surface;
#   their membership facts are handled by finite list-set membership.
# - Definition 3.1.4, equality of sets:
#   set equality is proved by extensionality, written `by extension A = B:`.
#   This is the proof interface used around several of the set axioms.
# - Axiom 3.4, pairwise union:
#   binary union is the object `union(A, B)`, with membership introduction and
#   elimination facts for the two sides.
# - Axiom 3.5, specification:
#   bounded set comprehension is `{x X: P(x)}`. Litex intentionally requires
#   the ambient set or type `X`.
# - Axiom 3.6, replacement:
#   relation-level replacement is the object `replacement(P, A)`. Function
#   images use the more direct surfaces `fn_range_on(f, A)` and the local
#   Section 3.4 templates for image notation.
# - Axiom 3.7, infinity:
#   the builtin natural-number set `N`, together with `0`, successor arithmetic,
#   and the Chapter 2 induction principles, is the working interface.
# - Axiom 3.8, unrestricted comprehension:
#   excluded. Litex has no universal-set builder; every comprehension remains
#   bounded by an ambient set or type.
# - Axiom 3.9, regularity/foundation:
#   the trusted preview proof step is `by regularity_axiom(A)` for a non-empty
#   set `A`.
# - Axiom 3.10, function sets:
#   Tao's `Y^X` is the function type `fn(x X) Y`; concrete functions are built
#   with `have fn ...`, often by cases on finite domains.
# - Axiom 3.11, union over a family:
#   the family-union object is `cup(F)`. Litex proves membership from a member
#   set witness and releases the existential witness from stored membership;
#   finite examples can then be closed by ordinary `by extension`.
# - Axiom of choice, not used yet:
#   later choice arguments use the trusted `by axiom_of_choice(...)` interface.
#
# Thus this chapter uses the ZF-facing surfaces already present in Litex, while
# deliberately omitting unrestricted comprehension and postponing choice until
# Section 8.4.

# The indexed-family templates above are the chapter-facing notation.  General
# beta-independence for the source definition of indexed intersections and
# broader finite-family theorem packaging belong in the reusable std/set-theory
# package.


# Analysis I, Chapter 3, Section 3.5: Cartesian products.
#
# 样章分节：这一节把 ordered pair、tuple 和 Cartesian product 翻译到 Litex
# 的 tuple/cartesian-product surface。Tao 的 set-theoretic construction
# 作为 source-facing 注释保留；主线不重建 Kuratowski pair。


# Ordered pairs and binary Cartesian products

"""
Definition 3.5.1. Ordered pairs remember order: (x,y)=(x',y') iff both
components agree. This differs from unordered pair sets.
"""

# Ordered pair 在 Litex 里直接用 tuple literal `(x,y)`；投影用 `[1]` 和 `[2]`。
# 这里不把 ordered pair 重新编码成 set，因为 Tao 自己也把 set-theoretic
# construction 放到 exercise。主线更需要的是 tuple 的接口。

sketch:
    forall x1, x2 set, y1, y2 set:
        x1 = x2
        y1 = y2
        =>:
            (x1, y1) = (x2, y2)

    forall x1, x2 set, y1, y2 set:
        (x1, y1) = (x2, y2)
        =>:
            x1 = (x1, y1)[1] = (x2, y2)[1] = x2
            y1 = (x1, y1)[2] = (x2, y2)[2] = y2

    (3, 5) = (2 + 1, 3 + 2)
    (3, 5)[1] = 3
    (3, 5)[2] = 5
    tuple_dim((3, 5)) = 2

    claim:
        ? (3, 5) != (5, 3)
        by contra:
            ? (3, 5) != (5, 3)
            (3, 5) = (5, 3)
            3 = (3, 5)[1] = (5, 3)[1] = 5
            impossible 3 = 5

    claim:
        ? (3, 5) != (3, 3)
        by contra:
            ? (3, 5) != (3, 3)
            (3, 5) = (3, 3)
            5 = (3, 5)[2] = (3, 3)[2] = 3
            impossible 5 = 3

    claim:
        ? (3, 5) != (2, 5)
        by contra:
            ? (3, 5) != (2, 5)
            (3, 5) = (2, 5)
            3 = (3, 5)[1] = (2, 5)[1] = 2
            impossible 3 = 2

"""
Remark 3.5.2 says ordered pairs can be constructed from set axioms.
"""

"""
Remark 3.5.3 notes that parentheses are overloaded again.
"""

"""
Definition 3.5.4. The Cartesian product X x Y consists of ordered pairs whose
first component lies in X and second component lies in Y.
"""

"""
Remark 3.5.5. We assume this is a set; set-theoretic construction is deferred
to an exercise.
"""

# Cartesian product corresponds to Litex `cart(X,Y)`.  The surface accepts
# ordinary set factors, including empty factors such as `cart({},Y)`, so the
# empty-factor convention follows Tao's binary product shape.  Litex is still
# stricter about arity: `cart` has at least two factors, so one-factor and
# zero-factor product conventions are not current `cart` syntax.
# Membership introduction is `(x,y) $in cart(X,Y)`; elimination from
# `p cart(X,Y)` gives each coordinate in the corresponding factor.

sketch:
    claim:
        ? forall X, Y nonempty_set, x X, y Y:
            (x, y) $in cart(X, Y)
        (x, y) $in cart(X, Y)

    claim:
        ? forall X, Y nonempty_set, p cart(X, Y):
            p[1] $in X
            p[2] $in Y
        p[1] $in X
        p[2] $in Y

    cart_dim(cart({}, {1})) = 2
    count(cart({}, {1})) = 0
    not $is_nonempty_set(cart({}, {1}))


# Product examples and functions on products

"""
Example 3.5.6. If X={1,2} and Y={3,4,5}, then X x Y and Y x X have the same
size but are different sets because coordinate order matters.
"""

# 这个例子适合直接写成 Litex：membership、projection、cardinality、以及
# `X x Y != Y x X` 都可以用 concrete finite sets 检查。

sketch:
    (1, 3) $in cart({1, 2}, {3, 4, 5})
    (2, 5) $in cart({1, 2}, {3, 4, 5})
    cart_dim(cart({1, 2}, {3, 4, 5})) = 2
    proj(cart({1, 2}, {3, 4, 5}), 1) = {1, 2}
    proj(cart({1, 2}, {3, 4, 5}), 2) = {3, 4, 5}
    count(cart({1, 2}, {3, 4, 5})) = count({1, 2}) * count({3, 4, 5}) = 6
    count(cart({3, 4, 5}, {1, 2})) = count({3, 4, 5}) * count({1, 2}) = 6

    claim:
        ? cart({1, 2}, {3, 4, 5}) != cart({3, 4, 5}, {1, 2})
        by contra:
            ? cart({1, 2}, {3, 4, 5}) != cart({3, 4, 5}, {1, 2})
            cart({1, 2}, {3, 4, 5}) = cart({3, 4, 5}, {1, 2})
            (1, 3) $in cart({1, 2}, {3, 4, 5})
            (1, 3) $in cart({3, 4, 5}, {1, 2})
            (1, 3)[2] $in {1, 2}
            (1, 3)[2] = 3
            3 $in {1, 2}
            not 3 $in {1, 2}
            impossible not 3 $in {1, 2}

"""
After Example 3.5.6, a function on X x Y can be viewed either as a function
of one pair variable or as a function of two variables. Tao treats these
perspectives as interchangeable in practice.
"""

# Litex supports both surfaces. A unary function on `cart(N,N)` takes one
# pair argument and projects its coordinates; a two-input function takes the
# same coordinates as separate arguments. The functions have different formal
# types, but they can express the same operation pointwise.

sketch:
    have fn cart_add_on_pair(p cart(N, N)) N = p[1] + p[2]
    have fn cart_add_two_inputs(x N, y N) N = x + y

    cart_add_on_pair((2, 3)) = 5
    cart_add_two_inputs(2, 3) = 5

    claim:
        ? forall x, y N:
            cart_add_on_pair((x, y)) = cart_add_two_inputs(x, y)
        cart_add_on_pair((x, y)) = (x, y)[1] + (x, y)[2]
        (x, y)[1] = x
        (x, y)[2] = y
        cart_add_on_pair((x, y)) = x + y
        cart_add_two_inputs(x, y) = x + y
        cart_add_on_pair((x, y)) = cart_add_two_inputs(x, y)

    cart_add_on_pair $in fn(p cart(N, N)) N
    cart_add_two_inputs $in fn(x N, y N) N


# Tuples and finite Cartesian products

"""
Definition 3.5.7. Ordered n-tuples generalize ordered pairs, and finite
Cartesian products collect tuples with the ith component in the ith factor.
"""

# Litex 对具体 tuple literal 和 finite cartesian product 已经有 builtin surface。
# 对于维度 `n` 已经在上下文里的对象，也可以用 coordinate-wise definition：
# `have tuple f by i <= n, f[i] = expr` 和
# `have cart C by i <= n, proj(C, i) = expr`。这里的 `i <= n` 内部表示
# `i closed_range(1,n)`；Litex 会检查 `n $in N_pos`、`2 <= n`，并释放对应的
# coordinate `forall` fact。这个语法很适合记录 Tao 的 n-tuple / finite product
# 直觉，但完整的“任意 finite family 的 product”接口仍然是更高一层的 API。

sketch:
    tuple_dim((1, 2, 3)) = 3
    (1, 2, 3)[1] = 1
    (1, 2, 3)[2] = 2
    (1, 2, 3)[3] = 3

    (1, 2, 3) $in cart({1, 2}, {2, 3}, {3, 4})
    cart_dim(cart({1, 2}, {2, 3}, {3, 4})) = 3
    proj(cart({1, 2}, {2, 3}, {3, 4}), 1) = {1, 2}
    proj(cart({1, 2}, {2, 3}, {3, 4}), 2) = {2, 3}
    proj(cart({1, 2}, {2, 3}, {3, 4}), 3) = {3, 4}

    have n N_pos = 3
    have tuple index_tuple by i <= n, index_tuple[i] = i
    $is_tuple(index_tuple)
    tuple_dim(index_tuple) = n
    forall i closed_range(1, n):
        index_tuple[i] = i

    have cart repeated_real_cart by i <= n, proj(repeated_real_cart, i) = R
    $is_set(repeated_real_cart)
    $is_cart(repeated_real_cart)
    cart_dim(repeated_real_cart) = n
    forall i closed_range(1, n):
        proj(repeated_real_cart, i) = R
    repeated_real_cart = cart(R, R, R)

"""
Remark 3.5.8 constructs finite products from function spaces and
specification.

Example 3.5.9. If X1={a1,b1}, X2={a2,b2}, and X3={a3,b3}, then the flat
product X1 x X2 x X3 contains triples, while the iterated binary products
(X1 x X2) x X3 and X1 x (X2 x X3) contain nested pairs.
"""

# Litex keeps these three product shapes separate.  Tao writes out all eight
# elements in each case; the checked version below records the eight membership
# facts and the common count, while also showing that the arities and
# projections differ.  The full eight-element RHS as a list-set literal is left
# as proof debt because Litex does not yet infer pairwise tuple inequality from
# component inequality strongly enough for list-set well-definedness.

sketch:
    forall a1, b1, a2, b2, a3, b3 set:
        a1 != b1
        a2 != b2
        a3 != b3
        =>:
            (a1, a2, a3) $in cart({a1, b1}, {a2, b2}, {a3, b3})
            (a1, a2, b3) $in cart({a1, b1}, {a2, b2}, {a3, b3})
            (a1, b2, a3) $in cart({a1, b1}, {a2, b2}, {a3, b3})
            (a1, b2, b3) $in cart({a1, b1}, {a2, b2}, {a3, b3})
            (b1, a2, a3) $in cart({a1, b1}, {a2, b2}, {a3, b3})
            (b1, a2, b3) $in cart({a1, b1}, {a2, b2}, {a3, b3})
            (b1, b2, a3) $in cart({a1, b1}, {a2, b2}, {a3, b3})
            (b1, b2, b3) $in cart({a1, b1}, {a2, b2}, {a3, b3})
            count(cart({a1, b1}, {a2, b2}, {a3, b3})) = 8

    forall a1, b1, a2, b2, a3, b3 set:
        a1 != b1
        a2 != b2
        a3 != b3
        =>:
            ((a1, a2), a3) $in cart(cart({a1, b1}, {a2, b2}), {a3, b3})
            ((a1, a2), b3) $in cart(cart({a1, b1}, {a2, b2}), {a3, b3})
            ((a1, b2), a3) $in cart(cart({a1, b1}, {a2, b2}), {a3, b3})
            ((a1, b2), b3) $in cart(cart({a1, b1}, {a2, b2}), {a3, b3})
            ((b1, a2), a3) $in cart(cart({a1, b1}, {a2, b2}), {a3, b3})
            ((b1, a2), b3) $in cart(cart({a1, b1}, {a2, b2}), {a3, b3})
            ((b1, b2), a3) $in cart(cart({a1, b1}, {a2, b2}), {a3, b3})
            ((b1, b2), b3) $in cart(cart({a1, b1}, {a2, b2}), {a3, b3})
            count(cart(cart({a1, b1}, {a2, b2}), {a3, b3})) = 8

    forall a1, b1, a2, b2, a3, b3 set:
        a1 != b1
        a2 != b2
        a3 != b3
        =>:
            (a1, (a2, a3)) $in cart({a1, b1}, cart({a2, b2}, {a3, b3}))
            (a1, (a2, b3)) $in cart({a1, b1}, cart({a2, b2}, {a3, b3}))
            (a1, (b2, a3)) $in cart({a1, b1}, cart({a2, b2}, {a3, b3}))
            (a1, (b2, b3)) $in cart({a1, b1}, cart({a2, b2}, {a3, b3}))
            (b1, (a2, a3)) $in cart({a1, b1}, cart({a2, b2}, {a3, b3}))
            (b1, (a2, b3)) $in cart({a1, b1}, cart({a2, b2}, {a3, b3}))
            (b1, (b2, a3)) $in cart({a1, b1}, cart({a2, b2}, {a3, b3}))
            (b1, (b2, b3)) $in cart({a1, b1}, cart({a2, b2}, {a3, b3}))
            count(cart({a1, b1}, cart({a2, b2}, {a3, b3}))) = 8

    forall a1, b1, a2, b2, a3, b3 set:
        a1 != b1
        a2 != b2
        a3 != b3
        =>:
            cart_dim(cart({a1, b1}, {a2, b2}, {a3, b3})) = 3
            cart_dim(cart(cart({a1, b1}, {a2, b2}), {a3, b3})) = 2
            cart_dim(cart({a1, b1}, cart({a2, b2}, {a3, b3}))) = 2
            proj(cart({a1, b1}, {a2, b2}, {a3, b3}), 1) = {a1, b1}
            proj(cart(cart({a1, b1}, {a2, b2}), {a3, b3}), 1) = cart({a1, b1}, {a2, b2})
            proj(cart({a1, b1}, cart({a2, b2}, {a3, b3})), 2) = cart({a2, b2}, {a3, b3})

"""
Remark 3.5.10. A finite ordered tuple is also called a finite sequence; later
chapters introduce infinite sequences.
"""

# 这个 remark 只需要保留定位。真正的 infinite sequence vocabulary 在 Chapter 5/6
# 才成为 analysis 主线。


# Product conventions and finite choice

"""
Example 3.5.11. One-fold products are essentially the underlying set, while
the empty product is the singleton containing the empty tuple.
"""

# Litex deliberately keeps `cart` as a product-space surface with at least two
# factors. It does not parse 1-tuples `(x)` as tuple objects, and it has no
# 0-tuple `()` object. The one-fold/empty-product conventions are
# finite-indexed product API proof debt, not current `cart` syntax.

"""
Lemma 3.5.12 (Finite choice). A finite product of non-empty sets is non-empty.
The proof is induction: choose from the first n sets, choose one more point,
then append it.
"""

# For Litex's current `cart` surface this lemma is a builtin structural fact:
# any fixed finite-arity `cart` expression is nonempty once all its factors are
# nonempty.  The fully Tao-shaped theorem over a variable finite family
# `(X_i)_{1<=i<=n}` still needs a finite-indexed product/family API, but the
# ordinary binary and ternary product cases below are checkable directly.
# The user can use `by induc` in Litex to prove that if all sets inside cart are nonempty, then the cart is nonempty, just like the original proof in textbook. But it's not necessary because Litex can do it for you.

sketch:
    forall X, Y nonempty_set:
        $is_nonempty_set(cart(X, Y))

    forall X, Y, W nonempty_set:
        $is_nonempty_set(cart(X, Y, W))

"""
Remark 3.5.13. Extending finite choice to infinitely many sets is not
automatic; it requires the axiom of choice, discussed later in Section 8.4.
"""

# proof_debt: add a reusable finite-indexed product/family API for the exact
# Tao statement over families `X_i nonempty_set` and products
# `prod_{1<=i<=n} X_i`.  Current `cart` already handles each written finite
# arity of at least two factors.


# Analysis I, Chapter 3, Section 3.6: Cardinality of sets.
#
# This section has two complementary routes.  Tao's source-facing definition
# of "same size" is existence of a bijection.  Litex's practical route for
# finite sets is the builtin `finite_set` and `count(X)` surface.  The sketch
# keeps both visible: bijections for equal cardinality, `count` for checked
# finite-cardinality calculations.

# Section 3.6 uses the injective/surjective/bijective vocabulary introduced in
# Section 3.3 above; the split-file duplicate definitions are removed here.

# Equal cardinality

"""
Definition 3.6.1. Two sets have equal cardinality iff there exists a bijection
from one set to the other.
"""

# The Litex predicate is exactly the source definition: a function witness
# together with injectivity and surjectivity.

prop has_equal_cardinality(S, T set):
    exist f fn(x S) T st {$is_bijective_fn(S, T, f)}

"""
Example 3.6.2. The sets {0,1,2} and {3,4,5} have equal cardinality.  A single
failed map from {0,1,2} to {3,4} does not yet prove that no bijection exists.
"""

# The first part constructs a concrete bijection by shifting each element up
# by 3.  The second part gives one non-bijection into `{3,4}` by showing it is
# not injective; the actual non-equicardinality is left to uniqueness.

sketch:
    have fn shift_0_to_3(n {0, 1, 2}) {3, 4, 5} by cases:
        case n = 0: 3
        case n = 1: 4
        case n = 2: 5

    shift_0_to_3(0) = 3
    shift_0_to_3(1) = 4
    shift_0_to_3(2) = 5

    claim:
        ? $is_injective_fn({0, 1, 2}, {3, 4, 5}, shift_0_to_3)
        by enumerate finite_set:
            ? forall x1, x2 {0, 1, 2}:
                shift_0_to_3(x1) = shift_0_to_3(x2)
                =>:
                    x1 = x2
        $is_injective_fn({0, 1, 2}, {3, 4, 5}, shift_0_to_3)

    claim:
        ? $is_surjective_fn({0, 1, 2}, {3, 4, 5}, shift_0_to_3)
        by cases:
            ? forall y {3, 4, 5}:
                exist x {0, 1, 2} st {y = shift_0_to_3(x)}
            case y = 3:
                witness exist x {0, 1, 2} st {y = shift_0_to_3(x)} from 0:
                    shift_0_to_3(0) = 3
                    y = 3
                    y = shift_0_to_3(0)
            case y = 4:
                witness exist x {0, 1, 2} st {y = shift_0_to_3(x)} from 1:
                    shift_0_to_3(1) = 4
                    y = 4
                    y = shift_0_to_3(1)
            case y = 5:
                witness exist x {0, 1, 2} st {y = shift_0_to_3(x)} from 2:
                    shift_0_to_3(2) = 5
                    y = 5
                    y = shift_0_to_3(2)
        $is_surjective_fn({0, 1, 2}, {3, 4, 5}, shift_0_to_3)

    $is_bijective_fn({0, 1, 2}, {3, 4, 5}, shift_0_to_3)
    witness exist f fn(x {0, 1, 2}) {3, 4, 5} st {$is_bijective_fn({0, 1, 2}, {3, 4, 5}, f)} from shift_0_to_3:
        $is_bijective_fn({0, 1, 2}, {3, 4, 5}, shift_0_to_3)
    $has_equal_cardinality({0, 1, 2}, {3, 4, 5})

    have fn collapse_to_two(n {0, 1, 2}) {3, 4} by cases:
        case n = 0: 3
        case n = 1: 3
        case n = 2: 4

    collapse_to_two(0) = 3
    collapse_to_two(1) = 3
    0 != 1
    by contra:
        ? not $is_bijective_fn({0, 1, 2}, {3, 4}, collapse_to_two)
        $is_bijective_fn({0, 1, 2}, {3, 4}, collapse_to_two)
        $is_injective_fn({0, 1, 2}, {3, 4}, collapse_to_two)
        collapse_to_two(0) = collapse_to_two(1)
        0 = 1
        impossible 0 = 1

    count({0, 1, 2}) = count({3, 4, 5}) = 3
    count({3, 4}) = 2

"""
Remark 3.6.3. The natural numbers have equal cardinality with the even natural
numbers by the map n |-> 2n, even though the even naturals form a subset of N.
"""

# To formalize "even natural number" without importing a standard-library
# parity predicate, this chapter uses the local definition `m = 2*k`.

prop is_even_nat(m N):
    exist k N st {m = 2 * k}

# The target set is then `{m in N : m is even}`.  Injectivity is cancellation
# after dividing by 2, and surjectivity unfolds evenness to get the preimage.

sketch:
    have even_N set = {m N: $is_even_nat(m)}
    even_N $subset N

    claim:
        ? forall n N:
            2 * n $in even_N
        witness exist k N st {2 * n = 2 * k} from n:
            2 * n = 2 * n
        $is_even_nat(2 * n)
        2 * n $in {m N: $is_even_nat(m)}
        2 * n $in even_N

    have fn double_to_even(n N) even_N = 2 * n

    forall t N:
        double_to_even(t) = 2 * t

    claim:
        ? $is_injective_fn(N, even_N, double_to_even)
        forall x1, x2 N:
            double_to_even(x1) = double_to_even(x2)
            =>:
                double_to_even(x1) = 2 * x1
                double_to_even(x2) = 2 * x2
                2 * x1 = 2 * x2
                x1 = (2 * x1) / 2 = double_to_even(x1) / 2 = double_to_even(x2) / 2 = (2 * x2) / 2 = x2
        $is_injective_fn(N, even_N, double_to_even)

    claim:
        ? $is_surjective_fn(N, even_N, double_to_even)
        claim:
            ? forall y even_N:
                exist x N st {y = double_to_even(x)}
            y $in even_N
            $is_even_nat(y)
            exist k N st {y = 2 * k}
            have by exist k N st {y = 2 * k}: k
            k $in N
            2 * k $in even_N
            witness exist x N st {y = double_to_even(x)} from k:
                y = 2 * k
                2 * k = double_to_even(k)
                y = double_to_even(k)
        $is_surjective_fn(N, even_N, double_to_even)

    $is_bijective_fn(N, even_N, double_to_even)
    witness exist f fn(x N) even_N st {$is_bijective_fn(N, even_N, f)} from double_to_even:
        $is_bijective_fn(N, even_N, double_to_even)
    $has_equal_cardinality(N, even_N)

    by contra:
        ? not 1 $in even_N
        1 $in even_N
        $is_even_nat(1)
        exist k N st {1 = 2 * k}
        have by exist k N st {1 = 2 * k}: k
        1 = 2 * k
        k = 1 / 2
        k $in N
        not 1 / 2 $in N
        impossible not 1 / 2 $in N

"""
Proposition 3.6.4. Equal cardinality is reflexive, symmetric, and transitive.
"""

# The checked proof here is reflexivity: the identity map is a bijection from a
# set to itself.  Symmetry and transitivity need reusable inverse-function and
# composition interfaces, so they are recorded as proof debt below.

sketch:
    claim:
        ? forall X set:
            $has_equal_cardinality(X, X)
        have fn id_X(x X) X = x
        claim:
            ? $is_injective_fn(X, X, id_X)
            forall x1, x2 X:
                id_X(x1) = id_X(x2)
                =>:
                    id_X(x1) = x1
                    id_X(x2) = x2
                    x1 = x2
        claim:
            ? $is_surjective_fn(X, X, id_X)
            claim:
                ? forall y X:
                    exist x X st {y = id_X(x)}
                witness exist x X st {y = id_X(x)} from y:
                    id_X(y) = y
                    y = id_X(y)
            $is_surjective_fn(X, X, id_X)
        $is_bijective_fn(X, X, id_X)
        witness exist f fn(x X) X st {$is_bijective_fn(X, X, f)} from id_X:
            $is_bijective_fn(X, X, id_X)

# proof_debt: prove the symmetric and transitive parts of Proposition 3.6.4
# from reusable inverse-function and composition interfaces.  The proof route
# is clear, but duplicating the whole inverse/composition package here would
# make this section harder to read.

# Finite cardinality

"""
Definition 3.6.5. A set has cardinality n when it has equal cardinality with a
standard n-element set.
"""

# Tao uses `{i in N : 1 <= i <= n}`.  This self-contained sketch uses
# `range(0, n)` as the Litex-native n-element index set; finite computations
# below still use `count(X)`.

prop has_cardinality(X set, n N):
    $has_equal_cardinality(X, range(0, n))

"""
Remark 3.6.6. One may use either a 0-indexed or a 1-indexed standard n-element
set when defining cardinality n.
"""

# The checked instance uses n=4.  The map `i |-> i+1` is written by cases and
# proved bijective between `{0,1,2,3}` and `{1,2,3,4}`.

sketch:
    have fn shift_zero_to_one(i {0, 1, 2, 3}) {1, 2, 3, 4} by cases:
        case i = 0: 1
        case i = 1: 2
        case i = 2: 3
        case i = 3: 4

    shift_zero_to_one(0) = 1
    shift_zero_to_one(1) = 2
    shift_zero_to_one(2) = 3
    shift_zero_to_one(3) = 4

    claim:
        ? $is_injective_fn({0, 1, 2, 3}, {1, 2, 3, 4}, shift_zero_to_one)
        by enumerate finite_set:
            ? forall x1, x2 {0, 1, 2, 3}:
                shift_zero_to_one(x1) = shift_zero_to_one(x2)
                =>:
                    x1 = x2
        $is_injective_fn({0, 1, 2, 3}, {1, 2, 3, 4}, shift_zero_to_one)

    claim:
        ? $is_surjective_fn({0, 1, 2, 3}, {1, 2, 3, 4}, shift_zero_to_one)
        by cases:
            ? forall y {1, 2, 3, 4}:
                exist x {0, 1, 2, 3} st {y = shift_zero_to_one(x)}
            case y = 1:
                witness exist x {0, 1, 2, 3} st {y = shift_zero_to_one(x)} from 0:
                    shift_zero_to_one(0) = 1
                    y = 1
                    y = shift_zero_to_one(0)
            case y = 2:
                witness exist x {0, 1, 2, 3} st {y = shift_zero_to_one(x)} from 1:
                    shift_zero_to_one(1) = 2
                    y = 2
                    y = shift_zero_to_one(1)
            case y = 3:
                witness exist x {0, 1, 2, 3} st {y = shift_zero_to_one(x)} from 2:
                    shift_zero_to_one(2) = 3
                    y = 3
                    y = shift_zero_to_one(2)
            case y = 4:
                witness exist x {0, 1, 2, 3} st {y = shift_zero_to_one(x)} from 3:
                    shift_zero_to_one(3) = 4
                    y = 4
                    y = shift_zero_to_one(3)
        $is_surjective_fn({0, 1, 2, 3}, {1, 2, 3, 4}, shift_zero_to_one)

    $is_bijective_fn({0, 1, 2, 3}, {1, 2, 3, 4}, shift_zero_to_one)
    witness exist f fn(x {0, 1, 2, 3}) {1, 2, 3, 4} st {$is_bijective_fn({0, 1, 2, 3}, {1, 2, 3, 4}, f)} from shift_zero_to_one:
        $is_bijective_fn({0, 1, 2, 3}, {1, 2, 3, 4}, shift_zero_to_one)
    $has_equal_cardinality({0, 1, 2, 3}, {1, 2, 3, 4})

"""
Example 3.6.7. Listed finite sets with distinct entries have the expected
cardinality.
"""

# Litex's practical finite-cardinality surface is `finite_set` plus `count`.

sketch:
    forall a, b, c, d set:
        a != b
        a != c
        a != d
        b != c
        b != d
        c != d
        =>:
            count({a, b, c, d}) = 4
            count({a}) = 1


# Uniqueness and count interfaces

"""
Proposition 3.6.8. If a finite set has cardinality n and cardinality m, then
n = m.
"""

# Litex's `count(X)` already packages the uniqueness result for finite sets:
# if two natural numbers are both equal to `count(X)`, they are equal.  The
# concrete `{0,1,2}` versus `{3,4}` line shows the later conclusion promised in
# Example 3.6.2.

sketch:
    forall X finite_set, n, m N:
        count(X) = n
        count(X) = m
        =>:
            n = m

    count({0, 1, 2}) != count({3, 4})

"""
Lemma 3.6.9. Removing one element from an n-element set leaves n-1 elements.
"""

# The current checked route proves the available finite-set facts: the deletion
# is finite and its count is at most the original count.  The exact `n-1`
# equality is kept as proof debt because it needs a reusable deletion theorem.

sketch:
    1 $in set_minus({1, 2, 3}, {2})
    3 $in set_minus({1, 2, 3}, {2})
    $is_finite_set(set_minus({1, 2, 3}, {2}))
    count(set_minus({1, 2, 3}, {2})) <= count({1, 2, 3})

# proof_debt: add a theorem for exact deletion:
# if `X finite_set`, `x in X`, then
# `count(set_minus(X, {x})) = count(X) - 1`.
# Also add the negative membership elimination used informally here:
# `not x $in set_minus(X, {x})`.


"""
Definition 3.6.10. A set has finite cardinality if it has cardinality n for
some natural number n; it has infinite cardinality otherwise.
"""

# These predicates preserve Tao's bijection-based wording.  The checked
# finite-set route below still uses Litex's builtin `finite_set` and `count`.

prop has_finite_cardinality(X set):
    exist n N st {$has_cardinality(X, n)}

prop has_infinite_cardinality(X set):
    not $has_finite_cardinality(X)

"""
Example 3.6.11. Small concrete finite-cardinality computations agree with the
expected counts.
"""

# These examples use Litex's `count` surface.  The final claim records that
# every Litex finite set has some natural-number count.

sketch:
    $is_finite_set({0, 1, 2})
    count({0, 1, 2}) = 3
    $is_finite_set({3, 4})
    count({3, 4}) = 2
    $is_finite_set({})
    count({}) = 0
    count({1, 2, 3, 4}) = 4
    count(range(0, 4)) = 4
    count(closed_range(1, 4)) = 4
    count(range(0, 4)) = count(closed_range(1, 4))

    claim:
        ? forall X finite_set:
            exist n N st {count(X) = n}
        count(X) $in N
        witness exist n N st {count(X) = n} from count(X):
            count(X) = count(X)

"""
Theorem 3.6.12. The natural numbers are infinite.  Tao's proof shows that a finite list of all
natural numbers would have a maximum M, so M+1 would be missing.
"""

# Litex can express the contradiction with `count(N)` directly: if N were
# finite, the finite interval `0...count(N)` would be a subset of N with
# `count(N)+1` elements, contradicting the count bound for subsets.

sketch:
    by contra:
        ? not $is_finite_set(N)
        $is_finite_set(N)

        forall x 0...count(N):
            x $in N

        0...count(N) $subset N

        count(N) + 1 = count(N) - 0 + 1 = count(0...count(N)) <= count(N)

        impossible count(N) + 1 <= count(N)

    not $is_finite_set(N)

# proof_debt: Tao's bounded-list proof needs a reusable theorem that every
# finite subset of N is bounded.

"""
Remark 3.6.13. The sets Q and R are also infinite by unboundedness, and
infinite cardinalities need not all be equal.
"""

# This section checks the N case above.  The Q/R examples and the "different
# sizes of infinity" claim belong to later ordered-field and
# countability/cardinality material.
# proof_debt: add a reusable theorem that an unbounded subset of an ordered
# natural-number-like or real-number-like set is infinite, then instantiate it
# for Q and R.


# Finite subsets and cardinal arithmetic

"""
Proposition 3.6.14. Finite cardinal arithmetic: adding a new element, finite
unions, finite subsets, finite images, Cartesian products, and function spaces
are finite with the expected cardinality bounds or formulas.
"""

# Many finite union/subset/product facts are already available through Litex's
# finite-set/count surface.  Images and function spaces need more std support,
# especially exact image counts and function-space count formulas.

sketch:
    claim:
        ? forall X, Y finite_set:
            $is_finite_set(union(X, Y))
            count(union(X, Y)) <= count(X) + count(Y)
        $is_finite_set(union(X, Y))
        count(union(X, Y)) <= count(X) + count(Y)

    claim:
        ? forall X, Y finite_set:
            intersect(X, Y) = {}
            =>:
                count(union(X, Y)) = count(X) + count(Y)
        count(union(X, Y)) = count(X) + count(Y) - count(intersect(X, Y))
        count(intersect(X, Y)) = count({})
        count({}) = 0
        count(union(X, Y)) = count(X) + count(Y)

    intersect({1, 2}, {3}) = {}
    count(union({1, 2}, {3})) = count({1, 2}) + count({3})
    count({3}) = 1
    count(union({1, 2}, {3})) = count({1, 2}) + 1 = 3

    claim:
        ? forall X finite_set, Y set:
            Y $subset X
            =>:
                $is_finite_set(Y)
                count(Y) <= count(X)
        by thm subset_of_finite_set_is_finite(Y, X)
        $is_finite_set(Y)
        count(Y) <= count(X)

    have fn double_on_three(n {1, 2, 3}) {2, 4, 6} by cases:
        case n = 1: 2
        case n = 2: 4
        case n = 3: 6

    $is_finite_set(fn_range_on(double_on_three, {1, 2, 3}))

    forall X, Y nonempty_set:
        $is_finite_set(X)
        $is_finite_set(Y)
        =>:
            $is_finite_set(cart(X, Y))
    forall X, Y nonempty_set:
        $is_finite_set(X)
        $is_finite_set(Y)
        =>:
            count(cart(X, Y)) = count(X) * count(Y)
    count(cart({1, 2}, {3, 4, 5})) = count({1, 2}) * count({3, 4, 5}) = 6
    count(cart({3, 4, 5}, {1, 2})) = count({3, 4, 5}) * count({1, 2}) = 6

"""
Remark 3.6.15. The preceding finite-cardinality facts explain the usual
arithmetic operations on finite cardinalities: disjoint union gives addition,
Cartesian product gives multiplication, and powersets/function spaces give
exponentiation.
"""

# The checked example here is the powerset side of exponentiation.  The general
# powerset and function-space formulas are still recorded as proof debt below.

sketch:
    count(power_set({1, 2, 3})) = 2^count({1, 2, 3}) = 8

# proof_debt:
# - general exact one-new-element count: `count(union(X, {x})) = count(X) + 1`
#   when `x` is not in X;
# - general finite image cardinality and equality for injective images;
# - finite function-space cardinality `count(Y^X) = count(Y)^count(X)`;
# - general finite power-set cardinality `count(power_set(X)) = 2^count(X)`;
# - pigeonhole principle and finite boundedness lemmas needed downstream.

```
