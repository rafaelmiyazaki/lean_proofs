# Proof-obligation ledger

**Paper:** Miyazaki, Mulrenin, Pohoată and Zheng, [*Improved Ramsey Bounds for Generalized Schur Equations*](https://arxiv.org/abs/2605.15147), arXiv:2605.15147v1.

**Trust convention:** `MainBoundPowered`, `ResidueCoveringPrinciple`, and `CVECoveringStatement` are *propositions* in this project. A Lean theorem taking one as a hypothesis proves an implication, not that hypothesis.

## Paper-level status

| Result | Current verification |
|---|---|
| Lemma 3.1, padding | **Unconditional Lean proof** |
| Section 3, signed representations and charge classes | **Unconditional Lean proofs** |
| Section 3, proper `2m+1` colorings of difference-graph radius-`m` balls | **Unconditional Lean proof** |
| Section 4, affine-residue obstruction equivalence | **Unconditional Lean proof** |
| Theorem 1.3, lower/optimality direction for all `r` | **Unconditional Lean proof** |
| Theorem 1.3, upper direction for `r=1,2` | **Unconditional Lean proofs** |
| Theorem 1.3, upper direction for general `r` | **Conditional** on Crittenden–Vanden Eynden covering theorem |
| Lemma 2.1, weighted local-coloring | **Unconditional Lean proof**; verified in 44619364740 and axiom-audited in 44620242041 |
| Theorem 1.1, quantitative bound | **Unconditional Lean proof compiled** in 44621193781; main declaration axiom audit pending |
| Corollary 1.2 | **Unconditional Lean proof compiled** in 44621193781; axiom audit pending |

## Lemma 2.1: precise status

| Piece | Source | Status |
|---|---|---|
| Exact real weight `1/(χ^d(d!)^(1/ell))`, positivity and antitonicity | `RealWeights.lean` | Verified |
| Sharp weight multiplier after losing a color | `WeightGain.lean` | Verified |
| Powered-weight factorial recurrence | `PoweredWeights.lean` | Verified |
| Slow-growth layer inequality | `SlowGrowth.lean` | Verified |
| Weighted finite-color averaging / heavy independent class | `HeavyClass.lean`, `ColorFiberMass.lean` | Verified |
| Heavy incident-color neighborhood | `HeavyNeighbor.lean` | Verified |
| Selected initial closed-neighborhood has mass strictly greater than `W/d` | `SeedMass.lean` | Verified |
| Incident color-degree monotonicity and strict drop | `ColorDegrees.lean` | Verified |
| Colored walks, radius layers and loss of color after layer deletion | `GraphLayers.lean`, `GraphLayerDeletion.lean` | Verified |
| Selected independent color class implies strict vertex reduction | `DeletionSize.lean` | Verified |
| Exact finite-set mass partition and lower bound after deletion | `MassAccounting.lean` | Verified |
| Mass preservation using **actual** real weights and explicit structural hypotheses | `WeightMassInductionStep.lean` | Verified **conditional implication** |
| Strong induction on vertex count | `MassInduction.lean` | Verified **conditional implication** |
| Numeric conclusion from total mass `≤1` | `FinalWeightBound.lean` | Verified **conditional implication** |
| Complete weighted bound from universal proper mass-nondecreasing deletion principle | `WeightedLemmaReduction.lean` | Verified **conditional implication** |
| Degree-one monochromatic star and full radius-one ball | `DegreeOneStar.lean` | **Unconditional Lean proofs compiled** |
| Heavy independent class from a proper local coloring | `HeavyIndependentClass.lean` | **Unconditional Lean proof compiled** |
| **Case d=1 of weighted deletion, mass-preserving and strictly smaller** | `DegreeOneMassStep.lean` | **Unconditional Lean implication compiled**, given the specified proper coloring |
| Strict mass-nondecreasing deletion for d≥2 | `DegreeGeTwoMassStep.lean` | **Unconditional proof compiled** |
| All-cases strict mass-nondecreasing deletion | `AllCasesDeletion.lean` | **Unconditional proof compiled** |
| Inheritance of local colorability and exact weights by induced subtypes | `InducedBallColoring.lean`, `InducedWeightTransport.lean` | **Unconditional proofs compiled** |
| Universal deletion over arbitrary induced vertex sets | `UniversalWeightedInduction.lean` | **Unconditional proof compiled** |
| Complete weighted Lemma 2.1 | `WeightedLemma21.lean` | **Unconditional proof compiled and axiom-audited** |

## Other obligations

The external [Crittenden–Vanden Eynden formalization](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos275.lean) is a possible dependency, but uses Lean 4.33 and has no declared license. It has not been imported, copied, or treated as an axiom.

`MainBoundPowered` and Corollary 1.2 are now compiled as unconditional proofs. The finite difference-graph application is in `FiniteDifferenceGraph.lean`, `FiniteDifferenceWalk.lean`, and `FiniteSchurRealBound.lean`; the natural powered bound and corollary are in `SchurPowerConversion.lean`, `MainTheorem11.lean`, and `Corollary12.lean`. Axiom audit of these final declarations is pending.

Review statement fidelity before declaring a complete paper formalization: number of colors, positivity, repeated summands, exact neighborhood definition, graph locality, and the constants in all bounds.

## Verification

The most recent successfully compiled source commit before this ledger update is [GitHub Actions run 44583357689](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44583357689), with **8,066 jobs**. That run includes every source file listed above. The extended axiom audit is part of the next commit. The final `#print axioms` results must be checked on that commit; `sorryAx` must be absent.

## New exact Case 1 verification

[GitHub Actions run 44588386054](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44588386054) successfully compiled the full minimum incident-color-degree-one branch: under the paper's local proper-coloring hypothesis, `degree_one_mass_preserving_induced_subgraph` constructs a proper induced subgraph with no smaller exact real total weight. The proof uses symmetry of the edge coloring, the uniform-color star, a heavy independent fiber, and the weighted graph deletion estimate. The case of minimum incident color-degree at least two remains open.

## November 19: main quantitative theorem completed

- [Run 44619364740](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44619364740) compiled Lemma 2.1. [Axiom audit 44620242041](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44620242041) shows only Lean standard axioms.
- [Run 44621193781](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44621193781) compiled the exact theorem `main_bound_powered : MainBoundPowered` and `corollary_1_2_unconditional` (8090 build jobs).
- The new `#print axioms` audit for the main theorem and corollary was added to `Audit.lean` in commit 1026a62. Its results must be checked before claiming a clean final audit.
- **Only independent mathematical theorem still required for the paper's main claims:** the classical Crittenden–Vanden Eynden progression covering theorem, needed to discharge the hypothesis of general Theorem 1.3 upper. A final statement-fidelity review remains necessary even after it is proved.
