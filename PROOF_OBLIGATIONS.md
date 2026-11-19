# Improved Ramsey Bounds for Generalized Schur Equations — Lean proof ledger

Source: Miyazaki, Mulrenin, Pohoată and Zheng, [arXiv:2605.15147v1](https://arxiv.org/abs/2605.15147) (2026).

**Verification method:** the Lean 4.28 + Mathlib kernel accepts the declarations after a successful `lake build` in GitHub Actions. The project's current green build should be inspected after each edit. Proofs with explicit mathematical hypotheses establish implications only.

| Manuscript item | Lean source | Verification |
|---|---|---|
| List-based equations and color classes | `Definitions.lean` | Elaborated definitions |
| Lemma 3.1 (padding) | `Padding.lean` | Unconditional proof compiled |
| Section 3 charge arithmetic | `Charge.lean` | Unconditional proofs compiled |
| Charge-class independence | `ChargeClasses.lean` | **Unconditional Lean proof compiled** |
| Coloring signed-reachable vertices using at most 2m+1 charge classes | `ChargeColoring.lean` | **Unconditional Lean proof compiled** |
| Color-graph walks produce signed representations | `ColorPaths.lean` | **Unconditional Lean proof compiled** |
| Color-radius-m balls admit proper 2m+1 colorings | `ColorPaths.lean` | **Unconditional Lean proof compiled** |
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
| Weighted local-coloring vertex-weight factorial update | `PoweredWeights.lean` | **Unconditional Lean proof compiled** |
| Slow-growth layer mass inequality | `SlowGrowth.lean` | Unconditional proof compiled |
| Final weighted deletion inequality | `WeightedDeletion.lean` | Unconditional proof compiled |
| Largest weighted color class (abstract and finite coloring) | `HeavyClass.lean`, `ColorFiberMass.lean` | Unconditional proofs compiled |
| Monotonicity and strict drop of incident color-degree | `ColorDegrees.lean` | Unconditional proofs compiled |
| Elimination of a selected edge color after deletion | `ColorDeletion.lean` | Unconditional proofs compiled |
| Colored graph walks, radius balls, and next-layer closure | `GraphLayers.lean` | Proof draft, CI in progress |
| Layer deletion directly from radius-ball geometry | `GraphLayerDeletion.lean` | Proof draft, CI in progress |
| Weighted local-coloring Lemma 2.1 | — | Graph-theoretic induction and total-weight estimate still unproved |
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
4. Formalize the colored-graph weighted lemma (Lemma 2.1). The charge-class independence, proper coloring, and walk-to-representation local-ball argument are now compiled.
5. Prove the main quantitative bound (Theorem 1.1), then discharge the assumption in Corollary 1.2.

## Trust policy

`MainBoundPowered`, `ResidueObstructionPrinciple`, and `ResidueCoveringPrinciple` are **definitions of propositions**. They are not proved merely because a theorem accepts them as arguments. Audit each claimed verified theorem using `#print axioms` and verify that its actual elaborated statement faithfully represents the manuscript (including positive intervals and repeated summands).

## Axiom auditing

`RMFormal/Schur/Audit.lean` prints Lean's reported axioms for each unconditional result. This is included in the root build. On GitHub Actions run 44524172688, all eight audited theorems reported only standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorryAx`.

## Latest verification

[GitHub Actions run 44532837172](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44532837172) passed all 8044 build jobs. Twelve unconditional theorem axiom audits showed only `propext`, `Classical.choice`, and `Quot.sound` (some with fewer); none showed `sorryAx`. The external covering theorem is still supplied only as an **explicit hypothesis** to `two_power_upper_of_cve`.

## Section 3 development

[GitHub Actions run 44541329817](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44541329817) compiled the `ChargeClasses.lean`, `ChargeColoring.lean`, and `ColorPaths.lean` modules. The new `#print axioms` entries are included in the next build; their audit results should be checked there.

## Weight-step arithmetic

The elementary identity for mth-powered weights was verified in [GitHub Actions run 44542819201](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44542819201). The unpowered vertex mass sum and the central inductive deletion argument are still missing; the powered identity alone is insufficient to establish Lemma 2.1.

## Latest verified audit, November 19, 2026

[GitHub Actions run 44543476720](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44543476720) passed all 8048 jobs. All **17** unconditional theorems audited in `Audit.lean` reported only standard Lean foundational axioms, with no `sorryAx`. This is not a claim that the two main research theorems are complete: Theorem 1.1 and the general upper half of Theorem 1.3 remain mathematically unproved in this repository.

## Weighted lemma subproofs, November 19

The slow-growth lemma, mass-preservation inequality, weighted color-class pigeonhole principle and color-degree deletion facts now have green source builds. Two more modules link these facts to actual color-radius balls: `GraphLayers.lean` and `GraphLayerDeletion.lean`. Their status must be established by a passing CI run. None of these partial results establishes Lemma 2.1 until the full finite-graph induction, including weight comparison after induced-vertex deletion, has been compiled.
