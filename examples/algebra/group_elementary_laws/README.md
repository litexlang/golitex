# Elementary group identities and self-inverse elements

A right identity is unique, and an idempotent group element is the identity.
An element squares to the identity exactly when it is its own inverse. These
results require neither commutativity nor a nontrivial carrier. The following
generic consumer states the right-identity theorem:

```litex
thm consume_right_identity_unique:
    ? forall A nonempty_set,G &Algebra::group::Group<A>,identity_candidate A:
        forall x A:
            G.mul(x,identity_candidate)=x
        =>:
            identity_candidate=G.one
    release thm Algebra::group::right_identity_unique(A,G,identity_candidate)
```

[main.lit](main.lit) constructs the additive group of the actual checked
two-element Field. Its element `1` is not the identity `0`, while `1+1=0`
and its group inverse is itself. [trivial](trivial/main.lit) checks the
one-element group; [contracts](contracts/main.lit) exercise all four results
over an arbitrary Group.

The [negative controls](negative/expected.json) reject missing premises and
false values for the nonidentity element. Run `python3
examples/algebra/group_elementary_laws/check.py --binary /path/to/litex
--output-dir /path/to/results` for strict, imported and installed checks.
