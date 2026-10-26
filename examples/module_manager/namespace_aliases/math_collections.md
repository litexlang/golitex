# Namespace identity model

The feature introduces no new mathematical objects, propositions or proof
rules. A namespace alias is a manifest-level abbreviation for the pair
(imported package, real exported file). Its purpose is stable short references
when packages add or reorder unrelated exports.

The representative interface is `[alias] C = Library::defs`, followed by
`C::value`, `$C::positive(1)`, `C::add_zero(2)`, `\C::copied<R>` and `&C::Pair`.
Each name retains the module/file/symbol identity of its full path. Definition
publication and proof checking keep their existing responsibilities; an alias
does not publish an imported fact or invent a declaration.

The nearest rejected forms are an alias chain, `Library::C::value` treating an
alias as an exported file, an undefined `C::ghost`, and the removed
`Library:::value` syntax. The acceptance library has two real exports with
different same-named values, so wrong-export selection cannot pass unnoticed.
There are no mathematical existence, uniqueness, domain or trust gaps added by
this feature.
