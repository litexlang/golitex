# Litex Local Code Style

Always apply these rules when working in this repository.

1. Write simple code, not clever code.

2. Use English for comments and documentation. Comments should be concise and to the point.

3. Do not write too many comments. If comments are needed, they should explain what the code is doing, not act as placeholders for code.

4. You may write functions, but never break the existing data structures.

5. Use `.into()` to convert between types instead of directly wrapping a struct with an enum variant such as `Enum::Variant(value)`.

6. Do not write static functions inside a struct when the struct is not needed. Use a pure free function instead.

7. Do not write too many functions. If a piece of code is simple and only called once, write it inside the function that calls it.

8. When writing Litex code, do not write an empty implication body for a `forall`. Write:

```litex
forall x R:
    ...
```

instead of:

```litex
forall x R:
    =>:
        ...
```

9. Any time the user asks for code that makes some Litex code verifiable, write the Litex code in `examples/tmp.lit` and test it, so the user can run it directly.

10. Any time you enhance a feature, check whether the documentation needs to be updated. If it does, update it in the same change.

11. When implementing a builtin rule, write comments about what mathematical property the rule is for, and include an example.

12. When implementing an infer rule, write comments about the condition under which the rule is applied and what new fact is inferred. Include an example.

13. Do not write code in `mod.rs`; `mod.rs` is only for module definitions.

14. Use `use crate::prelude::*;` to import repository modules instead of importing each module individually.

15. Always use `use crate::prelude::*;` for repository imports, except for `std` imports.

16. Do not use fancy Rust syntax.

17. Write shared helper functions in a `helper.rs` file, not at the head of a file. The head of a file should only be used for important things such as major functions or struct definitions.

18. Use a static `new` function to create a new instance of a struct instead of using the struct literal constructor directly.

19. Do not write new helper functions at the beginning of a file. Put them near the end of the file. The beginning of a file should only contain major functions or struct definitions.

20. If you change Litex syntax or semantics, update the documentation at the same time.

21. If a feature is new, put it into the preview feature section of the documentation.
