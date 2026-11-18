# Generalized Schur equations: formalization ledger

Source: Miyazaki, Mulrenin, Pohoată and Zheng, *Improved Ramsey Bounds for Generalized Schur Equations*, arXiv:2605.15147v1 (2026).

**Important:** These are Lean *drafts*. Until CI passes, even the simple proof scripts are unverified. Passing CI checks only the declarations actually included in the repository.

| Manuscript item | Lean source | Scope | Status |
|---|---|---|---|
| Basic sum equations and color classes | `Definitions.lean` | Exact list-based definitions | Draft; not compiled |
| Lemma 3.1 (padding) | `Padding.lean` | Repeat both sides and add common summands | Candidate proof; not compiled |
| Section 3 charge count equality | `Charge.lean` | Cross-count arithmetic | Candidate proof; not compiled |
| Section 4 sufficient residue obstruction | `ResidueClass.lean` | Nonzero class avoids all `(m+1,m)` equations | Candidate proof; not compiled |
| Corollary 1.2 | `Corollary.lean` | Conditional reduction given MainBoundPowered | Draft; conditional |
| Theorem 1.3 upper | `TwoPower.lean` | Conditional deduction from obstruction and covering principles | Draft; conditional |
| Theorem 1.3 lower | `Definitions.lean` | Proposition only | Not proved |
| Theorem 1.1 | `Definitions.lean` | Powered statement only | Not proved |
| Weighted local-coloring Lemma 2.1 | — | Major graph-theoretic proof | Not started |
| Affine obstruction necessary direction | `TwoPower.lean` | Explicit mathematical proposition, not proved | Not started |
| Crittenden–Vanden Eynden covering theorem | `TwoPower.lean` | Explicit mathematical proposition, not proved | Not started |

## Strict trust convention

Never call `MainBoundPowered`, `ResidueObstructionPrinciple`, or `ResidueCoveringPrinciple` a proved theorem unless it is constructed without unresolved assumptions. The statements are `def ... : Prop`. Conditional proofs with hypotheses certify *implications*, not the input propositions.

Run `lake build` and audit `#print axioms SchurFormal.some_theorem` for anything claimed formally verified. Also compare Lean statement details against the original paper: repetitions, positive intervals, color count, and quantifier scope.
