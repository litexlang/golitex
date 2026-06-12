# Litex Output Is Your Friend

### 

```litex
# Atomic fact verification route gallery.

# Direct builtin facts.
1 = 1
1 < 2
1 $in R
1 $in {1, 2}

# Facts introduced by object definitions, then cited again as atomic facts.
have x R = 1
x $in R
x = 1
x + 1 = 2

# A concrete prop definition can prove a prop fact.
prop is_one_tmp(t R):
    t = 1
$is_one_tmp(1)

# An unsafe known atomic fact, then the same predicate cited as a known fact.
abstract_prop known_p_tmp(t)
know $known_p_tmp(1)
$known_p_tmp(1)

# An unsafe known forall fact, then an atomic predicate proved by instantiation.
abstract_prop forall_p_tmp(t)
know:
    forall t R:
        t = 1
        =>:
            $forall_p_tmp(t)
$forall_p_tmp(1)

# A claim stores a prop fact; the following atomic line cites it.
prop claim_p_tmp(t R):
    t = 5
claim:
    prove:
        $claim_p_tmp(5)
    5 = 5
$claim_p_tmp(5)

# A theorem call stores a prop fact; the following atomic line cites it.
prop thm_p_tmp(t R):
    t = 4
thm thm_proves_p_tmp:
    prove:
        forall t R:
            t = 4
            =>:
                $thm_p_tmp(t)
    t = 4
by thm thm_proves_p_tmp(4)
$thm_p_tmp(4)

# A symmetric predicate registration lets the reversed atomic predicate cite
# the original known prop fact.
prop sym_p_tmp(u set, v set):
    u = v
by symmetric_prop:
    prove:
        forall u, v set:
            $sym_p_tmp(u, v)
            =>:
                $sym_p_tmp(v, u)
    u = v
    v = u
have A_tmp set
have B_tmp set
know $sym_p_tmp(A_tmp, B_tmp)
$sym_p_tmp(B_tmp, A_tmp)

# A reflexive abstract predicate registration proves a fresh atomic predicate
# through the registered property. The registration proof is intentionally
# unsafe so this file can isolate the output route.
abstract_prop refl_p_tmp(u, v)
by reflexive_prop:
    prove:
        forall u set:
            $refl_p_tmp(u, u)
    know $refl_p_tmp(u, u)
have C_tmp set
$refl_p_tmp(C_tmp, C_tmp)

# An existential fact can introduce a witness and its prop fact.
abstract_prop exists_p_tmp(t)
know exist m R st {$exists_p_tmp(m)}
have by exist m R st {$exists_p_tmp(m)}: witness_tmp
$exists_p_tmp(witness_tmp)

# Function definitions store function-space and equation facts; applications
# are atomic equality facts proved from that definition.
have fn id_tmp(t R) R = t
id_tmp(1) = 1


```

The output explains the proof process step by step. By looking at the output, you can actually 1. understand how litex verifies a fact 2. how a statement affects the context

```json
{
  "result": "success",
  "type": "equality fact",
  "line": 4,
  "statement": "1 = 1",
  "verification": {
    "type": "builtin rule",
    "rule": "same expression on both sides"
  },
  "store_facts": [
    {
      "fact": "1 = 1",
      "reason": "proved statement"
    }
  ]
}

{
  "result": "success",
  "type": "comparison fact",
  "line": 5,
  "statement": "1 < 2",
  "verification": {
    "type": "builtin rule",
    "rule": "number comparison"
  },
  "store_facts": [
    {
      "fact": "1 < 2",
      "reason": "proved statement"
    }
  ]
}

{
  "result": "success",
  "type": "membership fact",
  "line": 6,
  "statement": "1 $in R",
  "verification": {
    "type": "builtin rule",
    "rule": "number in R"
  },
  "store_facts": [
    {
      "fact": "1 $in R",
      "reason": "proved statement"
    }
  ]
}

{
  "result": "success",
  "type": "membership fact",
  "line": 7,
  "statement": "1 $in {1, 2}",
  "verification": {
    "type": "builtin rule",
    "rule": "list_set membership: equality with one listed element",
    "subgoals": [
      {
        "statement": "1 = 1 or 1 = 2",
        "verification": {
          "type": "builtin rule",
          "rule": "restricted builtin premise: one branch verified",
          "subgoals": [
            {
              "statement": "1 = 1",
              "verification": {
                "type": "cite equality fact",
                "cite_source": {
                  "line": 4
                },
                "cited_statement": "1 = 1"
              }
            }
          ]
        }
      }
    ]
  },
  "store_facts": [
    {
      "fact": "1 $in {1, 2}",
      "reason": "proved statement"
    }
  ]
}

{
  "result": "success",
  "type": "object definition",
  "line": 10,
  "statement": "have x R = 1",
  "store_facts": [
    {
      "fact": "x $in R",
      "reason": "object definition"
    },
    {
      "fact": "x = 1",
      "reason": "object definition"
    }
  ]
}

{
  "result": "success",
  "type": "membership fact",
  "line": 11,
  "statement": "x $in R",
  "verification": {
    "type": "cite membership fact",
    "cited_statement": "x $in R"
  },
  "store_facts": [
    {
      "fact": "x $in R",
      "reason": "proved statement"
    }
  ]
}

{
  "result": "success",
  "type": "equality fact",
  "line": 12,
  "statement": "x = 1",
  "verification": {
    "type": "cite equality fact",
    "cite_source": {
      "line": 10
    },
    "cited_statement": "x = 1"
  },
  "store_facts": [
    {
      "fact": "x = 1",
      "reason": "proved statement"
    }
  ]
}

{
  "result": "success",
  "type": "equality fact",
  "line": 13,
  "statement": "x + 1 = 2",
  "verification": {
    "type": "builtin rule",
    "rule": "calculation"
  },
  "store_facts": [
    {
      "fact": "x + 1 = 2",
      "reason": "proved statement"
    }
  ]
}

{
  "result": "success",
  "type": "predicate definition",
  "line": 16,
  "statement": "prop is_one_tmp(t R):\n    ~2t = 1"
}

{
  "result": "success",
  "type": "prop fact",
  "line": 18,
  "statement": "$is_one_tmp(1)",
  "verification": {
    "type": "cite prop def",
    "cite_source": {
      "line": 16
    },
    "cited_statement": "prop is_one_tmp(t R):\n    ~2t = 1",
    "detail": "prop with meaning `is_one_tmp` (param constraints and definition clauses)"
  },
  "store_facts": [
    {
      "fact": "$is_one_tmp(1)",
      "reason": "inferred by definition"
    }
  ]
}

{
  "result": "success",
  "type": "abstract predicate interface definition",
  "line": 21,
  "statement": "abstract_prop known_p_tmp(t)"
}

{
  "result": "success",
  "type": "unproved assumption",
  "line": 22,
  "statement": "know $known_p_tmp(1)",
  "store_facts": [
    {
      "fact": "$known_p_tmp(1)",
      "reason": "warning: unproved know assumption"
    }
  ]
}

{
  "result": "success",
  "type": "prop fact",
  "line": 23,
  "statement": "$known_p_tmp(1)",
  "verification": {
    "type": "cite prop fact",
    "cite_source": {
      "line": 22
    },
    "cited_statement": "$known_p_tmp(1)"
  },
  "store_facts": [
    {
      "fact": "$known_p_tmp(1)",
      "reason": "proved statement"
    }
  ]
}

{
  "result": "success",
  "type": "abstract predicate interface definition",
  "line": 26,
  "statement": "abstract_prop forall_p_tmp(t)"
}

{
  "result": "success",
  "type": "unproved assumption",
  "line": 27,
  "statement": "know forall t R:\n    ~1t = 1\n    =>:\n        $forall_p_tmp(~1t)",
  "store_facts": [
    {
      "fact": "forall t R:\n    ~1t = 1\n    =>:\n        $forall_p_tmp(~1t)",
      "reason": "warning: unproved know assumption"
    }
  ]
}

{
  "result": "success",
  "type": "prop fact",
  "line": 32,
  "statement": "$forall_p_tmp(1)",
  "verification": {
    "type": "cite forall fact",
    "cite_source": {
      "line": 28
    },
    "cited_statement": "forall t R:\n    ~1t = 1\n    =>:\n        $forall_p_tmp(~1t)",
    "instantiation": {
      "t": "1"
    },
    "requirements": [
      {
        "statement": "1 $in R",
        "verification": {
          "type": "cite membership fact",
          "cite_source": {
            "line": 18,
            "source_kind": "entry",
            "source": "entry"
          },
          "cited_statement": "1 $in R"
        }
      },
      {
        "statement": "1 = 1",
        "verification": {
          "type": "cite equality fact",
          "cite_source": {
            "line": 18
          },
          "cited_statement": "1 = 1"
        }
      }
    ]
  },
  "store_facts": [
    {
      "fact": "$forall_p_tmp(1)",
      "reason": "proved statement"
    }
  ]
}

{
  "result": "success",
  "type": "predicate definition",
  "line": 35,
  "statement": "prop claim_p_tmp(t R):\n    ~2t = 5"
}

{
  "result": "success",
  "type": "proved claim",
  "line": 37,
  "statement": "claim:\n    prove:\n        $claim_p_tmp(5)\n    5 = 5",
  "store_facts": [
    {
      "fact": "$claim_p_tmp(5)",
      "reason": "proved claim",
      "inferred_facts": [
        "5 $in R",
        "5 = 5"
      ]
    }
  ]
}

{
  "result": "success",
  "type": "prop fact",
  "line": 41,
  "statement": "$claim_p_tmp(5)",
  "verification": {
    "type": "cite prop fact",
    "cite_source": {
      "line": 39
    },
    "cited_statement": "$claim_p_tmp(5)"
  },
  "store_facts": [
    {
      "fact": "$claim_p_tmp(5)",
      "reason": "proved statement",
      "inferred_facts": [
        "5 $in R",
        "5 = 5"
      ]
    }
  ]
}

{
  "result": "success",
  "type": "predicate definition",
  "line": 44,
  "statement": "prop thm_p_tmp(t R):\n    ~2t = 4"
}

{
  "result": "success",
  "type": "theorem",
  "line": 46,
  "statement": "thm thm_proves_p_tmp:\n    prove:\n        forall t R:\n            ~1t = 4\n            =>:\n                $thm_p_tmp(~1t)\n    ~1t = 4"
}

{
  "result": "success",
  "type": "proof by theorem",
  "line": 53,
  "statement": "by thm thm_proves_p_tmp(4)",
  "store_facts": [
    {
      "fact": "$thm_p_tmp(4)",
      "reason": "theorem instantiation",
      "inferred_facts": [
        "4 $in R",
        "4 = 4"
      ]
    }
  ]
}

{
  "result": "success",
  "type": "prop fact",
  "line": 54,
  "statement": "$thm_p_tmp(4)",
  "verification": {
    "type": "cite prop fact",
    "cite_source": {
      "line": 53
    },
    "cited_statement": "$thm_p_tmp(4)"
  },
  "store_facts": [
    {
      "fact": "$thm_p_tmp(4)",
      "reason": "proved statement",
      "inferred_facts": [
        "4 $in R",
        "4 = 4"
      ]
    }
  ]
}

{
  "result": "success",
  "type": "predicate definition",
  "line": 58,
  "statement": "prop sym_p_tmp(u set, v set):\n    ~2u = ~2v"
}

{
  "result": "success",
  "type": "proof by symmetry",
  "line": 60,
  "statement": "by symmetric_prop:\n    prove:\n        forall u, v set:\n            $sym_p_tmp(~1u, ~1v)\n            =>:\n                $sym_p_tmp(~1v, ~1u)\n    ~1u = ~1v\n    ~1v = ~1u"
}

{
  "result": "success",
  "type": "object declaration",
  "line": 68,
  "statement": "have A_tmp set",
  "store_facts": [
    {
      "fact": "$is_set(A_tmp)",
      "reason": "object definition"
    }
  ]
}

{
  "result": "success",
  "type": "object declaration",
  "line": 69,
  "statement": "have B_tmp set",
  "store_facts": [
    {
      "fact": "$is_set(B_tmp)",
      "reason": "object definition"
    }
  ]
}

{
  "result": "success",
  "type": "unproved assumption",
  "line": 70,
  "statement": "know $sym_p_tmp(A_tmp, B_tmp)",
  "store_facts": [
    {
      "fact": "$sym_p_tmp(A_tmp, B_tmp)",
      "reason": "warning: unproved know assumption",
      "inferred_facts": [
        "$is_set(A_tmp)",
        "$is_set(B_tmp)",
        "A_tmp = B_tmp"
      ]
    }
  ]
}

{
  "result": "success",
  "type": "prop fact",
  "line": 71,
  "statement": "$sym_p_tmp(B_tmp, A_tmp)",
  "verification": {
    "type": "cite prop fact",
    "cite_source": {
      "line": 70
    },
    "cited_statement": "$sym_p_tmp(A_tmp, B_tmp)"
  },
  "store_facts": [
    {
      "fact": "$sym_p_tmp(B_tmp, A_tmp)",
      "reason": "proved statement",
      "inferred_facts": [
        "$is_set(B_tmp)",
        "$is_set(A_tmp)",
        "B_tmp = A_tmp"
      ]
    }
  ]
}

{
  "result": "success",
  "type": "abstract predicate interface definition",
  "line": 76,
  "statement": "abstract_prop refl_p_tmp(u, v)"
}

{
  "result": "success",
  "type": "proof by reflexivity",
  "line": 77,
  "statement": "by reflexive_prop:\n    prove:\n        forall u set:\n            $refl_p_tmp(~1u, ~1u)\n    know $refl_p_tmp(~1u, ~1u)"
}

{
  "result": "success",
  "type": "object declaration",
  "line": 82,
  "statement": "have C_tmp set",
  "store_facts": [
    {
      "fact": "$is_set(C_tmp)",
      "reason": "object definition"
    }
  ]
}

{
  "result": "success",
  "type": "prop fact",
  "line": 83,
  "statement": "$refl_p_tmp(C_tmp, C_tmp)",
  "verification": {
    "type": "builtin rule",
    "rule": "registered reflexive prop"
  },
  "store_facts": [
    {
      "fact": "$refl_p_tmp(C_tmp, C_tmp)",
      "reason": "proved statement"
    }
  ]
}

{
  "result": "success",
  "type": "abstract predicate interface definition",
  "line": 86,
  "statement": "abstract_prop exists_p_tmp(t)"
}

{
  "result": "success",
  "type": "unproved assumption",
  "line": 87,
  "statement": "know exist m R st {$exists_p_tmp(~3m)}",
  "store_facts": [
    {
      "fact": "exist m R st {$exists_p_tmp(~3m)}",
      "reason": "warning: unproved know assumption"
    }
  ]
}

{
  "result": "success",
  "type": "object definition by existence",
  "line": 88,
  "statement": "have by exist m R st {$exists_p_tmp(~3m)} : witness_tmp",
  "store_facts": [
    {
      "fact": "witness_tmp $in R",
      "reason": "exist elimination"
    },
    {
      "fact": "$exists_p_tmp(witness_tmp)",
      "reason": "exist elimination"
    }
  ]
}

{
  "result": "success",
  "type": "prop fact",
  "line": 89,
  "statement": "$exists_p_tmp(witness_tmp)",
  "verification": {
    "type": "cite prop fact",
    "cite_source": {
      "line": 88
    },
    "cited_statement": "$exists_p_tmp(witness_tmp)"
  },
  "store_facts": [
    {
      "fact": "$exists_p_tmp(witness_tmp)",
      "reason": "proved statement"
    }
  ]
}

{
  "result": "success",
  "type": "function definition",
  "line": 93,
  "statement": "have fn id_tmp(t R)= ~5t",
  "store_facts": [
    {
      "fact": "id_tmp $in fn (t R) R",
      "reason": "function definition"
    },
    {
      "fact": "id_tmp = '(t R) R {~5t}",
      "reason": "function definition"
    }
  ]
}

{
  "result": "success",
  "type": "equality fact",
  "line": 94,
  "statement": "id_tmp(1) = 1",
  "verification": {
    "type": "cite equality fact",
    "cite_source": {
      "line": 94
    },
    "cited_statement": "id_tmp(1) =1",
    "detail": "according to user-defined function `id_tmp(1)` = `1`"
  },
  "store_facts": [
    {
      "fact": "id_tmp(1) = 1",
      "reason": "proved statement"
    }
  ]
}

```
