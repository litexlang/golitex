# Appendix

Here’s a **short summary** of basic Litex elements, condensed for clarity:

---

### 1. **Mathematics Basics**
- **Sets and Types**: In Litex, a set is called a **type**, and its elements are called **first citizens**.
- **First Citizens**: Three kinds:
  1. **Variables**: Basic elements like `1`, `x`, or `1 + x`.
  2. **Functions**: Combine first citizens (propositions, variables, or other functions) into new first citizens, provided they satisfy the function's conditions.
  3. **Propositions**: Collections of factual expressions to be verified later by invoking their names.

---

### 2. **Types and Structures**
- **Types**: A type = a set + a structure.
  - Types in Litex work like types in programming languages (e.g., C, Go).
  - A set in math is a type with no structure, but sets like ℝ or ℕ have structures.
- **Structure**: Defined by elements (variables, functions, propositions) with specific properties.
  - Example: ℤ has structure with operations `+`, `-`, `*`, `/`, and identity `0`.
  - The same set can have different structures (e.g., `C[0,1]` with `L¹` vs. `L^∞` norms).
- **Relationships**: One type's structure can implement another's (e.g., ℝ implements ℂ's structure).
- **Generics**: Sets, i.e. types in Litex, can be parameters in propositions and functions, with conditions on types or elements.

---

### 3. **Concepts**
- A **concept** is a set of types with the same structure.
  - Example: A **group** is a set of sets with identity, inverse, and multiplication operations.
- A type can also implement a concept
  - Example: The set of real numbers is a ring.

---

### 4. **Factual Expressions**
- Three kinds:
  1. **Specific**: Existential or ordinary facts.
  2. **Conditional**: Facts with conditions.
  3. **Universal**: Facts using `forall`.

---

### 5. **Proof Methods**
- **Direct Proof**: Deriving new facts directly.
- **Proof by Contradiction**: Assuming the opposite to derive a contradiction.
  - This builds a bridge between existential facts and universal facts: not exist is equivalent to forall.

---

### 6. **Verification**
- Litex Uses **pattern-based matching** of known facts, allowing users no to explicitly name every fact. Verification is akin to searching a dictionary: you use a key to find relevant information.

---

### 7. **Mathematics vs. Programming**
- Math focuses on **search**, not execution.
- Existence of variables must be considered in math.
- **Litex types** are more powerful than programming types.

---


## Getting Started

Let us begin with a quick introduction to Litex. For the sake of pragmatism, our aim here is to show the essential elements of the language without getting bogged down in details, rules, and exceptions.

## First Example


<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 40%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 60%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>type Human</code> <br><br>
      <code>prop self_aware(x Human)</code> <br><br>      <code>know forall x Human:</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x is self_aware</code> <br> <br>
      <code>var Bob Human</code> <br> <br>
      <code>Bob is self_aware</code>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>def Human := Type</code> <br><br>
      <code>def self_aware (x : Human) : Prop := true</code> <br><br>
      <code>axiom self_aware_all :</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;∀ (x : Human), self_aware x</code> <br><br>
      <code>def Bob : Human := Human</code> <br><br>
      <code>example : self_aware Bob := self_aware_all Bob</code>
    </td>
  </tr>
</table>

For now, you don't need to understand everything; you only need to conceptually know what the example is doing. I put both Litex code and Lean4 (another popular proof assistant) code here to clarify fundamentals of Litex. We will refer to this example from time to time.

`Human` is a type representing all humans. Mathematically, you can think of `Human` as the set containing all humans. All humans are set to be `self_aware` by the user as a fact (i.e. true expression) using `know` keyword. `Bob` is `Human`. Therefore, `Bob is self_aware` is a true expression.

This is a classic example of syllogism (三段论), which demonstrates some core features and ideas of Litex very well. Notice Litex significantly reduces the amount of typing required by the user, involves fewer keywords and symbols, and is therefore more intuitive.

#### 1. In mathematics, there are only two things: sets and elements of sets.
1. **Type = Structure + Set**
   1. **Structure**: Operator overloading, members, type members.
      1. Structures allow types to establish relationships. For example, **R** can be viewed as **C**, which means **R** implements the structure of **C**.
         1. Inspiration comes from Go's `type` implementing an `interface`.
         2. Category theory might explain the implementation of structures, but it's not necessary to understand it to grasp the concept of implementation.
      2. Additional benefits:
         1. Encapsulates extra information, avoiding free variables like `n` in **R^n**.
   2. **Sets can have other sets as elements**: Achieved through **concept types**.
      1. Concepts carry extra information: multiple types may share the same structure, e.g., groups share the same structure.
   3. **An element belonging to a set**: The element has the type of the set.
   4. **Type overloading**: Types serve dual roles as sets and structures. This overloading is reasonable and avoids introducing extra keywords like "set."
   5. **Relationships between types**: Use `impl` to denote structural relationships. For example, if type **A** implements the structure of type **B**, use `impl`.
      1. If two types are equivalent as sets, use `forall` to establish variable correspondences. Use regular keywords for set-related properties and `impl` for structural properties.

#### 2. Three Basic Elements
1. **Prop**
2. **Var**
3. **Fn**
   1. Functions and variables can be merged since functions can do everything variables can.
   2. Functions are combinators of basic elements and do not execute.

#### 3. Three Types of Factual Expressions
1. **Specific**
   1. **Exist**
      1. Introduces variables and works with the `have` keyword.
      2. Otherwise behaves like `ordinary`.
   2. **Ordinary**
2. **Cond**
3. **Forall**
   1. Opens a local environment, substitutes variables, and verifies conditions.

#### 4. Four Outputs of Factual Expressions
1. Corresponds to four outputs when the human brain reads mathematics.
2. **Specific**

#### 5. Two Proof Methods: Prove and Prove by Contradiction
1. **Forall** and **exist** establish relationships in proof by contradiction.
2. **Prove**:
   1. Generates new facts.
   2. Establishes `type impl concept` or `type`.

#### 6. Verification Without Naming Every Fact
- Like querying a database, use patterns to search and match known facts for verification.

#### 7. Miscellaneous
1. Some facts are known by default.
2. Introducing variables is allowed by default.
3. Define new types, variables, functions, and propositions.
4. **Generics**:
   1. Pass types sets as parameters.
      1. Some types must meet conditions, e.g., a set must be a group.
   2. Adding conditions to variables is easier than to types because propositions and functions have `cond` for validation, while types do not.
      1. Although types cannot impose conditions directly, their elements can.
      2. A type's properties are determined by its elements (as a set) and its structure (members).
      3. Types are not passed like variables to avoid complexity and confusion, as types have the additional responsibility of structure.

#### 8. Differences Between Mathematics and Programming Languages
1. Mathematical verification does not require Turing completeness; it only needs search.
2. Mathematics requires `exist`, which programming languages do not.
3. **Litex** types have more responsibilities and capabilities than programming types.

#### 9. Differences Between Litex and Standard Mathematics
1. Sets cannot be passed like ordinary variables because they are types with additional information (bound members).

---

### Short Summary

1. **Mathematics**: Properties of sets and their items. In Litex, a set item is called a first citizen and a set is called a type.
2. **Basic Elements**: 3 kinds of first citizens: Propositions, variables, and functions. 
   1. Variables are basic elements of math. symbols like 1, x, 1 + x are all called variables.
   2. The role of functions is to combine several other first-class citizens (props, vars, fns) and form new first-class citizens.
      1. Only when first-citizens satisfy the condition of the function, they can be combined together into a single symbol using the function
      2. The combination of first-class citizens under a function are bound with extra features that appears in function definition.
   3. a proposition is a collection of factual expressions meant to be verified later by invoking its name
3. **Types and Concepts**: In Litex, type = set + structure.
   1. Types work very like how types work in everyday programming languages like C. Syntax of type works very much the same way as the Go programming language.
   2. You can understand a set in math as a type with no structure. However, sets like R and N do have structure.
   3. What do you mean by "structure"? 
      1. By analogy, in the language of programming, the members of a class in OOP (Object-Oriented Programming) represent the structure of the class.
      2. In analogy to mathematics, a **structure** is also defined through **elements** (such as variables, functions and propositions) with given properties.
         1. e.g. Z has structure: it has operator +, -, *, /, and 0.
   4. The same set can have different structures. 
      1. e.g. C[0,1] with L^1 norm or L^{\infinity} norm has different structure, thus have different properties. However, they are the same as set.
   5. Relationships between types
      1. the structure of one type might implement another type's structure
         1. e.g. R implements structure of C, so items in R are also in C.
4. A set of types with the same structure is called concept.
   1. Group is a set of sets that have identity, inverse operation, and multiplication operation.
5. **Factual Expressions**: Specific (exist, ordinary), conditional, and universal (`forall`).
6. **Proof Methods**: Direct proof and proof by contradiction, generating new facts.
7. **Verification**: Pattern-based matching of known facts, without naming every fact.
8.  **Generics**: Sets as parameters, with conditions on types or elements.
9.  **Mathematics vs. Programming**: Math focuses on search and existence, not execution. **Litex** types are more powerful than programming types.
10. **Litex vs. Standard Math**: Sets (as types) cannot be passed like variables due to their structural responsibilities.