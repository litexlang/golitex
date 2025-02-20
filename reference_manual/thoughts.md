25.2.19
1. fn domain == fn cond
2. fn type in principle should include cond. but since we use C-like struct(no parameter in type) instead of Rust-like type(you can use generics to have parameters in type), if you want to express "fn is a fn that has a domain that satisfies properties xxx ", you should give that class of functions a name and make it a new type. In short you should not pass parameters in type. You should make it a new type.
3. Rn is a concept, not type. Rn is a concept and it has member dim nat. Group is a concept, not type, it has member *, inverse, 1. They are all concepts. But in practice, mathematicians write R^{n} to represent a Rn and write G is Group instead of G^{*,inv,1}. REMEMBER ANY "TYPE" THAT HAS A PARAMETER IS A CONCEPT, WRITTEN IN XXX{parameters} IN DAILY WRITING.
e.g.
concept Rn S:   // suppose S is a Rn
    type_member:
        var dim Pos_Nat // dim is positive natural number
    member:
        fn \_\_at\_\_(n Pos_Nat) Real: // define @, which means the nth index of the vector. Notice the return type is Real
    cond:
        forall v1 S, v2 S:
            forall k Pos_Nat:
                cond:
                    k <= S.dim
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

4. The benefit of using concept is that you can write fn [s T] x s, y s to ensure x and y are eql type. The user should define what does x = y mean when x and y are of the same type, just like C++ programmers define == in class.
5. There is a major difference between template in C++ and concept in Litex: the template T must be initialized when used as parameter of a type. But member of a type of a concept needn't, because it's usually the member, not the instantiation of that member, has relation with other members and has some properties.
6. = is a special kind of prop. besides facts that the user defines to be equal to =, there are builtin ways to check =: 1. when a and b are literally the same 2. when b is alias of a. 3. you don't need to implement = every time you define a new type, = is automatically generated for you, just like = is automatically by C++ for you when you define a class without defining it.
7. as for vector plus vector, it works very like how it works in programming:
Litex:
// Define the result of summing 2 vectors
know forall [S Rn] v1 S, v2 S:
    forall k Pos_Nat:
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
8. type in Litex works like set in math. In Litex has one single responsibility: own member and type_member, as in all programming languages. member is owned by variable and type_member is owned by type itself. It's essential for operator overloading. . Actually, type in ordinary programming languages also works like set in math.
9. concept == type of type
10. ! I should give user keyword commutative and associative otherwise Litex can not verify (v1 + v2)@k = v2@k + v1@k even we we know (v1 + v2)@k = v1@k + v2@k
11. IMPORTANT: every time you encounter x of y, it means you should give a member to y called x. That is why OOP is very important in Litex
12. set is builtin concept, nat and pos_nat and float is builtin type Litex
13. you can view concept as set of sets; view type as set
13. the difference between concept and type is concept is a type of type (set of set), and type is one specific set. For example, nat is a type, because there is one set called natural numbers. group is a concept, because there are many groups.
13. such expression as "S is a set of variables of type Y" occurs very often. in litex it writes like
var S Set:
    $Set.type[Y]
14.The essence of the concept and type system in Litex is to break down a set represented by composed symbols in natural language into simpler **concepts** and **types**. This process is analogous to decomposing a complex structure (like a `struct` in programming) into smaller, more manageable substructures. Just as you might access a member of a higher-level struct using multiple dots (e.g., `structA.structB.member`), Litex allows you to retrieve or define components of a higher-level concept by breaking it down into its constituent parts.

### Example Breakdown:
Given the expression:  
**"forall c and d are real numbers and S = [1,2]*[c,d]"**, Litex decomposes it as follows:

1. **Define a concept for a product space**:  
   A product space is a concept that consists of two sets, `left` and `right`.  
   ```plaintext
   concept product_space:
       type_member:
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


