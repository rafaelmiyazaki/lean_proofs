# Improved Ramsey Bounds for Generalized Schur Equations — Lean proof ledger

Source: Miyazaki, Mulrenin, Pohoată and Zheng, [arXiv:2605.15147v1](https://arxiv.org/abs/2605.15147) (2026).

**Verification method:** the Lean 4.28 + Mathlib kernel accepts the declarations after a successful `lake build` in GitHub Actions. The project's current green build should be inspected after each edit. Proofs with explicit mathematical hypotheses establish implications only.

| Manuscript item | Lean source | Verification |
|---|---|---|
| List-based equations and color classes | `Definitions.lean` | Elaborated definitions |
| Lemma 3.1 (padding) | `Padding.lean` | Unconditional proof compiled |
| Section 3 charge arithmetic | `Charge.lean` | Unconditional proofs compiled |
| Section 4 sufficient residue obstruction | `ResidueClass.lean` | Unconditional proof compiled |
| Corollary 1.2 | `Corollary.lean` | Compiled **conditional** deduction assuming Theorem 1.1 |
| Theorem 1.3 lower, all r | `DyadicLower.lean` | **Unconditional proof compiled** |
| Theorem 1.3 upper, r=1 | `SmallCases.lean` | Unconditional proof compiled |
| Theorem 1.3 upper, r=2 | `SmallThresholds.lean` | Unconditional proof compiled |
| Theorem 1.3 upper, arbitrary r | `TwoPower.lean` | Compiled **conditional** deduction |
| Theorem 1.1 | `Definitions.lean` | Statement only; not proved |
| Integer-affine relation implies a Schur equation | `AffineRelation.lean` | Unconditional proof compiled |
| Explicit difference certificate gives a Schur equation | `DifferenceCertificate.lean` | Unconditional proof compiled |
| Finite-list Bézout identity | `BezoutList.lean` | Unconditional proof compiled |
| Gcd of integer list divides every entry | `BezoutList.lean` | Candidate proof; CI pending |
| Gcd-one difference obstruction | `GcdOne.lean` | Unconditional proof compiled |
| Weighted local-coloring Lemma 2.1 | — | Not formalized |
| Affine obstruction converse | `TwoPower.lean` | Explicit unproved principle |
| Crittenden–Vanden Eynden covering theorem | `TwoPower.lean` | Explicit unproved principle in this project |

## External proof opportunity

The covering theorem is **already formalized elsewhere** in [plby/lean-proofs / Erdős Problem 275](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos275.lean), using Lean 4.33 / Mathlib 4.33. The upstream code has no declared license. Do not copy it without clarifying permission. Our principle must still be shown to follow from the external statement even if its source eventually becomes available as a dependency.

## Remaining stages

1. Complete the **arbitrary-gcd case** of the affine-obstruction converse. The gcd-one case and finite Bézout coefficients are proved.
2. Connect the covering theorem to `ResidueCoveringPrinciple` with compatible Lean and Mathlib versions.
3. Complete the general upper direction of Theorem 1.3.
4. Formalize the colored-graph weighted lemma (Lemma 2.1).
5. Prove the main quantitative bound (Theorem 1.1), then discharge the assumption in Corollary 1.2.

## Trust policy

`MainBoundPowered`, `ResidueObstructionPrinciple`, and `ResidueCoveringPrinciple` are **definitions of propositions**. They are not proved merely because a theorem accepts them as arguments. Audit each claimed verified theorem using `#print axioms` and verify that its actual elaborated statement faithfully represents the manuscript (including positive intervals and repeated summands).

## Axiom auditing

`RMFormal/Schur/Audit.lean` prints Lean's reported axioms for each unconditional result. This is included in the root build. CI success plus an audit free of `sorryAx` is required for future proof-completion claims.
