25.2.19
1. fn domain == fn cond
2. fn type in principle should include cond. but since we use C-like struct(no parameter in type) instead of Rust-like type(you can use generics to have parameters in type), if you want to express "fn is a fn that has a domain that satisfies properties xxx ", you should give that class of functions a name and make it a new type. In short you should not pass parameters in type. You should make it a new type.
3. Rn is a concept, not type. Rn is a concept and it has member dim nat. Group is a concept, not type, it has member *, inverse, 1. They are all concepts. But in practice, mathematicians write R^{n} to represent a Rn and write G is Group instead of G^{*,inv,1}. REMEMBER ANY "TYPE" THAT HAS A PARAMETER IS A CONCEPT, WRITTEN IN XXX{parameters} IN DAILY WRITING.
e.g.
concept Rn S:   // suppose S is a Rn
    type_member:
        var dim Nat // dim is positive natural number
    member:
        fn \_\_at\_\_(n Nat) Real: // define @, which means the nth index of the 
            cond:
                n < S.dim
    cond:
        forall v1 S, v2 S:
            forall k Nat:
                (v1 + v2)@k = v1@k + v2@k
        

concept Group G: // suppose G is a group
    type_member:
        fn \_\_mul\_\_(g G, g2 G) G // define *
        var I G // define identity
    member:
        fn inv() G
    cond:
        forall v1 G, v2 G, v3 G: // equivalent to G.\_\_mu\_\_ is associative 
            (v1 * v2) * v3 = v1 * (v2 * v3)
        forall v G:
            v * v.inv() = G.I
            v.inv() * v = G.I

1. The benefit of using concept is that you can write fn [s T] x s, y s to ensure x and y are eql type. The user should define what does x = y mean when x and y are of the same type, just like C++ programmers define == in class.
2. There is a major difference between template in C++ and concept in Litex: the template T must be initialized when used as parameter of a type. But member of a type of a concept needn't, because it's usually the member, not the instantiation of that member, has relation with other members and has some properties.
3. = is a special kind of prop. besides facts that the user defines to be equal to =, there are builtin ways to check =: 1. when a and b are literally the same 2. when b = a. 3. you don't need to implement = every time you define a new type, = is automatically generated for you, just like = is automatically by C++ for you when you define a class without defining it.
4. as for vector plus vector, it works very like how it works in programming:
Litex:
// Define the result of summing 2 vectors
know forall [S Rn] v1 S, v2 S:
    forall k Nat:
        cond:
            k <= S.dim
        (v1 + v2)@k = v1@k + v2@k
Python:
// Return the result of summing 2 vectors
def vector_add(v1, v2):
    if len(v1) != len(v2):
        raise ValueError("Vectors must be of the same length")
    result = []
    for i in range(len(v1)):
        result.append(v1[i] + v2[i])
    return result
1. type in Litex works like set in math. In Litex has one single responsibility: own member and type_member, as in all programming languages. member is owned by variable and type_member is owned by type itself. It's essential for operator overloading. . Actually, type in ordinary programming languages also works like set in math.
2. concept == type of type
3.  ! I should give user keyword commutative and associative otherwise Litex can not verify (v1 + v2)@k = v2@k + v1@k even we we know (v1 + v2)@k = v1@k + v2@k
4.  IMPORTANT: every time you encounter x of y, it means you should give a member to y called x. That is why OOP is very important in Litex
5.  set is builtin concept, nat and pos_nat and float is builtin type Litex
6.  you can view concept as set of sets; view type as set
7.  the difference between concept and type is concept is a type of type (set of set), and type is one specific set. For example, nat is a type, because there is one set called natural numbers. group is a concept, because there are many groups.
8.  such expression as "S is a set of variables of type Y" occurs very often. in litex it writes like
var S Set:
    $Set.type[Y]

2.20
14.The essence of the concept and type system in Litex is to break down a set represented by composed symbols in natural language into simpler **concepts** and **types**. This process is analogous to decomposing a complex structure (like a `struct` in programming) into smaller, more manageable substructures. Just as you might access a member of a higher-level struct using multiple dots (e.g., `structA.structB.member`), Litex allows you to retrieve or define components of a higher-level concept by breaking it down into its constituent parts.

### Example Breakdown:
Given the expression:  
**"forall c and d are real numbers and S = [1,2]*[c,d]"**, Litex decomposes it as follows:

1. **Define a concept for a product space**:  
   A product space is a concept that consists of two sets, `left` and `right`.  
   ```plaintext
   concept product_space:
    nnn   type_member:
           var left set
           var right set
   ```

2. **Define a concept for an interval**:  
   An interval is a concept that consists of two real numbers, `left` and `right`.  
   ```plaintext
   concept interval:
       type_member:
           var left Real
           var right Real
   ```

3. **Apply the concepts to the given expression**:  
   For all instances of `S` that are of type `product_space`, the following conditions must hold:  
   - The `left` and `right` members of `S` must be intervals.  
   - The `left` interval of `S` must have `left = 1` and `right = 2`.  
   ```plaintext
   forall [S product_space]:
       cond:
           $interval(S.left)
           $interval(S.right)
           S.left.left = 1
           S.left.right = 2
   ```

### Explanation:
- **Concepts**: These are high-level abstractions (e.g., `product_space`, `interval`) that define the structure of types.  
- **Types**: These are the specific instances or members of a concept (e.g., `left` and `right` in `interval`).  
- **Decomposition**: The expression `S = [1,2]*[c,d]` is broken down into its constituent parts using the defined concepts and types.  
  - `S` is a `product_space` with `left` and `right` members.  
  - `S.left` is an interval `[1,2]`, and `S.right` is an interval `[c,d]`.  
  - The conditions ensure that the structure adheres to the defined concepts and types.
- **No need to specify c and d**:  In Litex, the forall in natural language corresponds to free variables, which do not require explicit initialization. This allows direct access to their members (e.g., .left and .right) through the structure of concepts and types. This design makes Litex more flexible and concise.

This system allows for a clear, hierarchical representation of complex ideas by breaking them down into simpler, reusable components.

15. Rust explicitly encodes all possible states in its type system using nested generics (e.g., `Result<Option<Vec<Result<T, E>>>, io::Error>`), forcing the caller to handle errors at compile time. In contrast, C uses simple type names but hides complexity inside structs, requiring manual checks and documentation to interpret NULL values and error codes. Rust ensures safety and clarity aka "minimalism when debugging", while C prioritizes "minimalism at first sight for its reader" but increases debugging complexity. In math, there is simply too many layers of abstraction that it's nearly impossible to explicit encode all states in its type system like Rust. What's more, Litex has 0 requirement for traditional debugging, SO I ADOPT C's type philosophy.

16. I guess It's reasonable to use "set" instead of "type" as "type declaration keyword" because set has a much stronger mental hind. the word "type" is rarely used in Math. And "inherit" in Litex is represented "subset_of". "subset" is used in type and concept, for example forall \[RnBall subset(Rn) \]  .

17. There is no control flow in Litex. THAT IS THE MAIN CORE BEHIND NEARLY ALL OF THE DIFFERENCE OF PL AND LITEX.
e.g.
    1. no traditional sense of debugging
    2. no need to worry about traditional sense of efficiency of Litex(because many "speed tests" use speed of loops and if-elses to measure)

18. claim == writing return value on the top line of a "function"

19. type overload == type implement interface in go == type impl concept. 
e.g. // Builtin concepts and types
concept OrdinalNumber
concept Set:
    type_member:
        var size OrdinalNumber
know Nat impl OrdinalNumber

// a set is finite
$Nat(s)
// empty set
set EMPTYSET
know EMPTYSET.size = 0

2.21
1. There are only a relatively small number of famous software written in functional programming languages. A huge reason is that they are poor at modularity. They require the user to be smart enough, they encourage the programmer to write "smart" while unmaintainable code.
2. Functional languages are by themselves hard to understand. People can write locally smart code while write globally unsustainable code. Math is already very hard, traditional formal proof languages which all based on functional programming languages makes it even harder.
3. I think the separation of passing type and passing interface (in C++, it means passing template in <> and pass variables in ()) is really necessary. Type can be "guessed" by the interpreter from the variables, but variables are called only when they are called.

prop human(x any)
prop mortal(x any)

know forall x any:
    cond:
        x is human
    then:
        $mortal(x)

var shen any
know shen is human
shen is mortal

import "real"

know forall x real, y real:
    cond:
        y < 0
    then:
        x + y < x

forall b real:
    -1 + b < b

-1 + 2 < 2

` vs lean4, litex is much much simpler
import Mathlib.Data.Real.Basic

theorem add_pos_gt {a b : ℝ} (h : b > 0) : a + b > a :=
begin
  calc a + b > a + 0 : by { apply add_lt_add_left, exact h }
         ... = a     : by { rw add_zero }
end

-- use add_pos_gt to prove -1 + b < b
theorem neg_one_add_lt {b : ℝ} (h : b > 0) : -1 + b < b :=
begin
  have h1 : -1 + b > -1, from add_pos_gt h,
  linarith,
end

example : -1 + 2 < 2 :=
begin
  apply neg_one_add_lt,
  norm_num,
end
`

2.22
1. never try to pass parameters to types. Such Type< Type< Type<> >, Type<>> would not lead to necessary complexity. People never get used to generics programming. Stick to one word type name like C instead.
2. Maybe my readme for now is a good introduction of Litex when Litex is well-known. But certainly, for now, my readme is just too hard to understand and my focus on "design philosophy" seems to be very strange and lofty when nothing concrete is introduced.

2.23
1. type hierarchy makes "a type implements a concept" or "a set satisfies requirements of a set of sets" (e.g. Integers are group. Here integer is a type and group is a concept) extremely hard for the users to write.
2. people no longer need to worry about naming overload, which occurs very often when you read poorly-written math books
3. math itself is cot, that is why training LLMs on Litex is very reasonable
4. A good piece of code or textbooks keeps the reader "guessing" what is next and feeling natural about they does guess correctly. Even when they don't guess correctly, they still quickly understand what is correct and why they failed to guess.
5. Build connections between 2 packages: first prove 2 things in each package is equivalent (concept, type, prop), then only prove theories about one thing, and at the end of the program says "this theory applies to the other thing"
6. If you worry facts about one thing are too many, give it a name, and only use the name name to prove theories and at the end of the program says "this theory applies to the other thing".
7. MAJOR UPDATE: interface in go is used to be "implemented" by types. If the type of a given parameter implements the interface(in this case: have all the required methods of that interface). SO CONCEPT ACTUALLY DOES NOT MEAN GENERICS IN LITEX, INSTEAD IT MEANS INTERFACE. HOWEVER, I still should not give up on passing type parameters and just using concept name because 2 types that both implement that concept and I should make sure it is THAT THE SAME type that is used as parameter type.
e.g. 
prop group_multiply_commutative\[ G Group\] (g1 G, g2 G):
    g1 * g2 = g2 * g1

// If only us concept
prop group_multiply_commutative(g1 Group, g2 Group): // g1 and g2 might belong to 2 different groups, which is not our intention.
    g1 * g2 = g2 * g1

8. Concepts do not usually come as self-contained entities. On the contrary , most concepts relate to other concepts in a variety of ways

2.26
1. exist a typeName :  $p(x, y) 

prop relation(x typeName2)
exist_prop y typeName has_relation_with(x typeName2):
    y < x

have $has_relation_with(x): y


var 1 Nat
var 2 Nat 
var 3 Nat

var-regex [0-9]* Nat

1p

(a + b)^ 2 = (a + b) * (a + b) = a * (a+b) + b * (a + b) =
a^2 + 2 * a * b + b ^ 2

<!-- fn introduction -->

typeName1 impl conceptName:
    proof:
        ....

prop math_induc:

know forall p prop:
    $math_induc(p)

Alice is human
human(Alice) is red
1 + 2 = 3
$=(1+ 2, 3)
$Real.__equal__(1+2,3)

f(1 < 2) 

self define bool

f(a bool)

return value of factual expressions goes to another world, can not use f(1 < 2) here, please by yourself define bool first

more examples