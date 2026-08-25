# Litex Developer Terminology

This document is the naming contract for Litex implementation code. It is
about Rust architecture, files, modules, tests, and developer prose; it does
not rename Litex source keywords or terms belonging to another language.

## Definition is the umbrella term

A **definition** is any reusable named entity or binding persisted in an
`Environment`. This includes objects, functions, predicates, settings,
templates, structures, algorithms, theorems, axioms, and strategies.

Use these related terms precisely:

- **definition header**: name, parameters, carrier/type/domain, and other
  signature-level information;
- **binding**: the association between a source name, scope, and `SymbolId`;
- **predicate**: a reusable `prop` or `abstract_prop` definition;
- **fact**: a concrete proposition that can be checked and stored;
- **introduction**: a standard logical introduction rule or witness
  construction, never a synonym for storing a Litex definition;
- **declaration**: an external or target-language term, such as a Lean
  declaration or a Rust module declaration, not Litex core storage.

The core route is therefore:

```text
Stmt::Definition(DefinitionStmt::...)
  -> definition_execution
  -> Environment.definitions: EnvironmentDefinitionRegistry
  -> SuccessStmtResult::Definition(SuccessDefinitionStmtResult::...)
```

Object definitions execute under `definition_execution/object`. Existential
elimination that creates object bindings is named explicitly; logical witness
execution remains in `witness_execution.rs`.

## Storage suffixes

Use suffixes by ownership, not by taste:

| Suffix | Meaning |
| --- | --- |
| `Registry` | Owns named registrations and identity lookup. |
| `Store` | Owns canonical semantic payloads. |
| `Index` | Secondary lookup derived from canonical payloads. |
| `Cache` | Recomputable acceleration state. |
| `Repository` | Filesystem or module-loading boundary. |

Accordingly, the environment owns `EnvironmentDefinitionRegistry`,
`EnvironmentFactStore`, and `EnvironmentStoredFactStore`; it does not call
those in-memory owners declaration registries, databases, or repositories.

## Parameter model names

Parameter model types describe collections and groups, so their names say so:

- `TypedParameterList` and `TypedParameterGroup` represent parameters whose
  carrier is a `ParamType`;
- `SetBoundParameterList` and `SetBoundParameterGroup` represent function
  parameters bound by set-valued domains.

Short names that mirror concrete Litex syntax may remain on leaf statement
types (`Obj`, `Fn`, `DefThmStmt`, and similar). Conceptual architecture,
modules, and cross-cutting APIs use full words.

## Compatibility boundaries

This migration deliberately preserves:

- every accepted Litex source keyword and program;
- JSON v2 field layout and exact statement `kind` strings;
- existing result-graph role strings such as `DefObjStmt` where they are part
  of serialized output;
- generated Lean meaning and the Lean compiler's `declarations: Vec<String>`,
  because those values really are Lean declarations;
- standard proof terminology such as disjunction, existential, universal, and
  set-membership introduction.

Compatibility strings do not authorize reintroducing matching Rust enums or
fields.

## Migration acceptance record

The migration started from commit `3a17b411b` on 2026-08-25.

Before:

```text
Stmt::DefObjStmt
  -> execute/object_introduction
  -> Environment.declarations
  -> SuccessStmtResult::DefObjStmt
```

Now:

```text
Stmt::Definition
  -> execute/definition_execution/object
  -> Environment.definitions
  -> SuccessStmtResult::Definition
```

The stable tracer is
[`examples/03_language_features/let_object_definition.lit`](../examples/03_language_features/let_object_definition.lit).
Its source and JSON v2 output are compatibility evidence; source-architecture
tests guard the internal naming contract.
