# Appendix

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
   1. Pass sets as parameters.
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

1. **Mathematics**: Comprises sets and their elements. 
2. **Basic Elements**: Propositions, variables, and functions. They are written as symbols. The role of functions is to take in several other basic elements (props, vars, fns) and form new symbols.
3. **Types and Concepts**: In Litex, sets are represented by types.Types combine structures and sets, allowing relationships like **R** implementing **C**. A set of types with the same structure is called concept.
4. **Factual Expressions**: Specific (exist, ordinary), conditional, and universal (`forall`).
5. **Proof Methods**: Direct proof and proof by contradiction, generating new facts or relationships.
6. **Verification**: Pattern-based matching of known facts, without naming every fact.
7. **Generics**: Sets as parameters, with conditions on types or elements.
8. **Mathematics vs. Programming**: Math focuses on search and existence, not execution. **Litex** types are more powerful than programming types.
9. **Litex vs. Standard Math**: Sets (as types) cannot be passed like variables due to their structural responsibilities.