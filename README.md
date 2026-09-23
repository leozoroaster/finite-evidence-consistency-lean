# Finite-evidence consistency in Lean 4

Lean 4/mathlib verification of the main characterization and stabilization
proposition in *An Order-Theoretic Characterization of Consistent Inductive Inference*
(September 2026 manuscript).

## Verified statement

For an arbitrary domain and binary hypothesis class, one learner makes finitely
many mistakes for every fixed target and every input sequence if and only if
there is one strict linear order on finite realizable traces such that:

1. Conflicting traces have different least subtraces.
2. The order is well-founded on the traces of each fixed target.

The main declaration is
[`FiniteEvidence.finiteEvidence_characterization_relation`](FiniteEvidenceConsistency.lean).
The order is chosen once for the whole class, and its minimum selector is derived,
not assumed. There is no finiteness or countability restriction, uniform mistake
bound, or global well-foundedness assumption. Empty domains and classes are
included. The proof uses the standard classical foundations of Lean.

## Verification scope

This repository formalizes the main characterization (Theorem 2.1), stabilization
of evidence (Proposition 4.1), and their supporting lemmas—not the entire paper.
The later propositions on target codes and countable domains (Proposition 4.2)
and consistency without a hypothesis-wise bound (Proposition 4.3, the
ordinal-threshold separation example) are not formalized here. The discussions
of computability and ZF/choice are also outside this formalization.

## Build and verify

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
bash scripts/verify.sh
```

Lean and mathlib are pinned to `v4.32.0`; `lake-manifest.json` records exact
dependency commits. Verification builds the proof, checks guarded axiom reports,
and replays all eight proof modules using Lean's kernel. The only axioms used by
the audited results are `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof placeholders or added mathematical axioms. Kernel replay is
an additional check, not an independently implemented verifier.

[GitHub Actions](https://github.com/leozoroaster/finite-evidence-consistency-lean/actions)
runs the same checks on a fresh checkout; generated logs and dependency caches
are not part of the repository.

## Proof map

All declarations below are in the `FiniteEvidence` namespace. Labels use `Bool`;
ordered histories use lists, while traces use finite sets.

| Paper component | Lean declaration | Source |
| --- | --- | --- |
| Definitions; order implies consistency | `Consistent`, `order_implies_consistent` | [Core](FiniteEvidence/Core.lean) |
| Canonical transcripts, replay, comparison | `transcript_replay`, `transcript_comparison` | [Canonical](FiniteEvidence/Canonical.lean) |
| Tree-order well-foundedness | `kb_wellFounded`, `target_transcripts_wellFounded` | [KleeneBrouwer](FiniteEvidence/KleeneBrouwer.lean), [MistakeTree](FiniteEvidence/MistakeTree.lean) |
| Consistency implies order | `consistent_implies_order` | [Converse](FiniteEvidence/Converse.lean) |
| Least-subtrace construction | `selectedMinimum`, `select_eq_selectedMinimum` | [Minimum](FiniteEvidence/Minimum.lean) |
| Main characterization (Theorem 2.1) | `finiteEvidence_characterization_relation` | [Main](FiniteEvidenceConsistency.lean) |
| Stabilization and decoder agreement (Proposition 4.1) | `stabilization_and_agreement` | [Stabilization](FiniteEvidence/Stabilization.lean) |

[`Audit.lean`](Audit.lean) displays the main statement and core definitions, and
rejects any change to the permitted axiom dependencies of twelve key results.
