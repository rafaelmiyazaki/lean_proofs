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
| Gcd of integer list divides every entry | `BezoutList.lean` | Unconditional proof compiled and axiom-audited |
| Gcd-one difference obstruction | `GcdOne.lean` | Unconditional proof compiled |
| Weighted local-coloring Lemma 2.1 | — | Not formalized |
| Affine obstruction converse | `ResidueNecessity.lean` | **Unconditional Lean proof compiled** |
| Complete finite affine-obstruction equivalence | `ResidueNecessity.lean` | **Unconditional Lean theorem compiled and axiom-audited** |
| Crittenden–Vanden Eynden covering theorem | `CoveringBridge.lean` | Explicit external theorem statement; not proved in this project |
| Theorem 1.3 upper given the classical covering theorem | `CoveringBridge.lean` | **Conditional theorem compiled**; external theorem unproved in this repository |

## External proof opportunity

The covering theorem is **already formalized elsewhere** in [plby/lean-proofs / Erdős Problem 275](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos275.lean), using Lean 4.33 / Mathlib 4.33. The upstream code has no declared license. Do not copy it without clarifying permission. Our principle must still be shown to follow from the external statement even if its source eventually becomes available as a dependency.

## Remaining stages

1. **Completed:** the arbitrary-gcd affine-obstruction converse, including the zero-gcd/singleton case. A combined equivalence has been **compiled and axiom-audited**.
2. Verify the bridge from the precise Crittenden–Vanden Eynden covering statement to `ResidueCoveringPrinciple`; its proof is currently conditional on the external theorem.
3. Complete the general upper direction of Theorem 1.3.
4. Formalize the colored-graph weighted lemma (Lemma 2.1).
5. Prove the main quantitative bound (Theorem 1.1), then discharge the assumption in Corollary 1.2.

## Trust policy

`MainBoundPowered`, `ResidueObstructionPrinciple`, and `ResidueCoveringPrinciple` are **definitions of propositions**. They are not proved merely because a theorem accepts them as arguments. Audit each claimed verified theorem using `#print axioms` and verify that its actual elaborated statement faithfully represents the manuscript (including positive intervals and repeated summands).

## Axiom auditing

`RMFormal/Schur/Audit.lean` prints Lean's reported axioms for each unconditional result. This is included in the root build. On GitHub Actions run 44524172688, all eight audited theorems reported only standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorryAx`.

## Latest verification

[GitHub Actions run 44532837172](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44532837172) passed all 8044 build jobs. Twelve unconditional theorem axiom audits showed only `propext`, `Classical.choice`, and `Quot.sound` (some with fewer); none showed `sorryAx`. The external covering theorem is still supplied only as an **explicit hypothesis** to `two_power_upper_of_cve`.
