# Function preimages

The selected interface has two set-valued objects. `preimage(f, y)` collects every legal input whose output equals the object `y`. `preimage_set(f, Y)` collects every legal input whose output belongs to the set `Y`. The point target may itself be a set; the constructor name, rather than the target's representation, determines equality versus membership. The scope contains no new image operator.

## Semantic contract

Let a checked complete function signature have fixed parameter carriers `A1, ..., An`, guards `G`, and return bound `B`. Its legal input assignment set `D` contains precisely the inputs satisfying those carriers and guards. For one parameter an input assignment is the input object itself. For several parameters it is an ordered tuple with exactly that arity. `D` and `apply` below are mathematical notation, not new source objects.

```text
preimage(f, y)     = {t in D | apply(f, t) = y}
preimage_set(f, Y) = {t in D | apply(f, t) in Y}

preimage(f, y) = preimage_set(f, {y})
```

Both results are sets, without an injectivity, surjectivity, or nonempty-fiber premise. They never choose one root. A unary function taking a tuple receives that whole tuple as its one argument. Multiple parameters use ordered coordinates; curried functions retain their call layers. A returned function such as `F(a)` can itself be passed as `f`.

The return bound is an upper bound, not the actual image. `y` need only be WD, and `Y` need only be a WD set. They need not lie in the declared return bound. An outside target produces a valid construction; proving that its preimage is empty is a separate obligation.

## Existing domain contracts

The [complete-domain consumer](../src/execute/execute_fact_stmt/function_domain.rs) derives signatures from checked memberships, anonymous functions, finite functions, templates, and callable application results. Equality to a function-space set supplies a set alias, not a callable value. Keep the exact source certificate and checked equality transports.

Current parameter carriers and return carriers cannot refer to their signature's own parameter names. Guards and expression bodies can. The [Manual](Manual.md) and [signature-scope tests](../tests/unit/parse/function_signature_scopes.rs) specify that boundary. Some older `FnSet` comments describe dependent returns more broadly; this feature preserves the current parser and WD contract.

```text
Supported signature shape: fn(a R, b R: b != 0) R
Rejected signature shape:  fn(S power_set(R), x S) R
Rejected signature shape:  fn(x R) {x}
```

## Object representation

The two leaves belong to the existing `FunctionSpace` family in the [AST](../src/ast/obj.rs):

```rust
pub struct Preimage {
    pub function: Box<Obj>,
    pub value: Box<Obj>,
}

pub struct PreimageSet {
    pub function: Box<Obj>,
    pub target_set: Box<Obj>,
}
```

`FunctionSpace::Preimage` and `FunctionSpace::PreimageSet` retain the distinct public forms. Parsing writes their operands; display, substitution, WD, truth verification, JSON and graph traversal read them. Domain signatures and proof scopes belong in verifier results. No new Env/Runtime state or changes to Stmt, Fact, Identifier, FnSet, or SetBuilder fields are part of this interface.

## Well-definedness and bounded construction

Check both children before selecting a complete callable domain. Point preimages check the target object's WD. Set preimages additionally retain target sethood. Every WD source object has sethood in the pure-set model; this does not introduce a universal source set of all objects.

For a unary signature `fn(x A: G(x)) B`, the construction uses the existing bounded builder:

```text
preimage(f, y)     -> {x A: G(x), f(x) = y}
preimage_set(f, Y) -> {x A: G(x), f(x) in Y}
```

The signature's guards are installed in the local proof scope before checking application WD. Thus a reciprocal on nonzero reals never forms an illegal call at zero while constructing either preimage. Multiple parameters bound an input tuple in the Cartesian product of the fixed carriers, substitute its coordinates in every guard, and form the original call layer.

The [construction pipeline](../src/execute/execute_fact_stmt/function_preimage.rs) retains its chosen complete-domain source, bounded builder, and builder WD proof. Existing [binder WD](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/binder.rs) owns and retains the local environment. The two outer WD proof variants mirror the two AST leaves and retain children before construction evidence. Success proofs contain only successful stages; soft failures preserve child or bounded-construction diagnostics.

An empty target cannot rescue an undefined or noncallable function, or an ill-defined target expression. WD proves that the set construction is legal, not that it is nonempty or that a candidate input is a member.

## Membership verification and inference

```text
t in preimage(f, y)
    iff t is a legal assignment and apply(f, t) = y

t in preimage_set(f, Y)
    iff t is a legal assignment and apply(f, t) in Y
```

The membership strategies check the carrier conditions, guards, and final output condition directly from the certified construction. They retain each requirement and its proof. They do not introduce an extra builder-membership premise or reset verifier permissions. Authors provide meaningful value equalities or output-membership evidence when ordinary bounded reasoning needs them; the constructors do not solve arbitrary equations for roots.

A known literal tuple is unpacked using its exact arity and checked equality path. Each coordinate's carrier and every guard remain proof obligations. This avoids manufacturing extra coordinate calls when the actual input values are already available. For a general tuple assignment, the bounded Cartesian membership and projections remain visible.

Stored membership directly projects the certified input carriers and guards, followed by the output equality or membership. Internal generated builder binders remain in WD evidence rather than being published as extra mathematical membership facts. Point and set projection results retain the exact source FactId, checked set-alias equality path, construction proof, and derived storage result. Local binder identities and facts do not escape their owning WD scopes.

Named, imported, anonymous, template, field, finite, and returned function values use the existing domain and equality interfaces. A function alias must have its own published callable signature or a directly recorded anonymous-function value. `let alias = f` alone does not authorize reading f's indexed signature through the equality; use an ordinary typed binding such as `have alias fn(x R) R = f` and the actual checked value equations. Do not select signatures or imported owners by display strings. The existing `have by fn_preimage` statement continues to extract a witness from known range membership; these objects denote complete input subsets and do not select witnesses.

## Primary acceptance example

The maintained tracer is [function_preimages.lit](../examples/wd/function_preimages.lit). It covers both reciprocal interfaces, exposed nonzero guards, a noninjective square function, aliases, and multiple parameters. Its required clean gate is:

```bash
target/release/litex -strict -lang en -f examples/wd/function_preimages.lit
```

Require exit zero and Normal JSON `kind: run`, `success: true`, and `session_error: null`. Verification status and materially distinct proof attempts belong in the paired [journal](../examples/wd/proof_journals/function_preimages_2026-10-08.json).

## Acceptance boundaries

| Case | Required behavior |
| --- | --- |
| Reciprocal at `1/2` | Input `2` belongs to both point and singleton-set preimages. |
| Membership in reciprocal preimages | Exposes real membership, nonzero guard, and the respective output condition. |
| Square at `4` | Both `-2` and `2` are members; no unique-root selection. |
| A target that itself is a set | Point preimage uses equality to that set; set preimage uses membership in the supplied set. |
| Empty or outside-return target | Construction is WD; unsupported emptiness assertions remain separate proof obligations. |
| Noncallable or invalid child | WD rejects before truth search, including with an empty target. |
| Multiple parameters | Exact tuple arity, carrier order, guards, and call layer retained. |
| Unary tuple argument | Whole tuple passed to the one parameter. |
| Aliases and imported functions | Canonical owners and checked equality paths retained. |
| Invalid root or guard violation | Membership rejects and the live Session retains prior accepted facts. |
| Malformed constructor arity | Parser rejects and rolls back tentative bindings. |

A finite target does not imply a finite preimage. A constant function on `R` has an infinite fiber at its constant output. Cardinality and broad set-algebra theorems are separate extensions.

## Integration and validation

The affected owners are the AST and binary primary parser; structural IR, alpha equality, congruence, substitution and LaTeX; complete-domain consumption and WD; membership strategies and storage inference; JSON descriptions and the generated typed graph visitor.

The public syntax and AST change is L4. Run focused positive, negative, alias, tuple, and rollback tests first; then the strict tracer, complete release Rust tests, and relevant executable documentation gates. Locate the actual generator before updating generated visitors. Preserve all unrelated worktree changes and local-only scripts.

## Lean boundary

This feature does not select a new Lean function ABI or add compiler support. A future backend must preserve the exact legal assignment carrier, point semantic equality versus set membership, source FactIds, guards, and local WD scopes. Until the reviewed function/set representation and proof adapters exist, unsupported constructors and proof routes must fail closed. No universal object ABI, project axiom, proof hole, or target-side root search follows from this interface.
