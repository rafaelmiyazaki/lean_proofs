# Lean formalizations — Rafael Miyazaki

Lean 4 / Mathlib formalization of mathematical results, beginning with **Miyazaki, Mulrenin, Pohoată and Zheng**, [*Improved Ramsey Bounds for Generalized Schur Equations*](https://arxiv.org/abs/2605.15147).

**Status: the quantitative Theorem 1.1 and Corollary 1.2 are kernel-compiled; Theorem 1.3's general upper direction is still conditional on an external covering theorem, so the paper as a whole is not yet completely formalized.** The branch `schur-formalization-draft` is a draft pull request. See [the proof ledger](PROOF_OBLIGATIONS.md) and [machine-readable status](VALIDATION.json).

## Unconditionally checked results

- Padding lemma, integer affine sign splitting, finite-list Bézout certificates.
- Exact affine-residue characterization of finite sets avoiding all `(m+1,m)` Schur equations.
- Theorem 1.3 lower/optimality direction for all positive `r` via a dyadic coloring; upper direction for `r=1,2`.
- Charge-class independence and a proper `2m+1` coloring of monochromatic difference-graph radius-`m` balls.
- Numerical, real-weight and finite-graph ingredients of Lemma 2.1: factorial weight update, monotonicity, sharp gain from losing a color, slow-growth layer, finite weighted averaging, explicit graph-layer deletion, exact mass accounting, strict vertex reduction, strong induction, and extraction of the `χ^q(q!)^(1/ell)` bound **from the mass hypothesis**.
- Heavy incident-color selection and the strict `W/d` lower bound for the selected closed neighborhood.

All statements named above have Lean proof scripts with no `sorry` or custom `axiom`; a passing build checks them. **The full weighted local-coloring Lemma 2.1 has now been proved and axiom-audited.**

## Compiled but conditional results

- **Theorem 1.3 upper half (all `r`)**: `two_power_upper_of_cve` assumes the Crittenden–Vanden Eynden covering theorem; the covering theorem has **not** been proved or imported into this project.
- **Corollary 1.2**: `corollary_1_2_of_main_bound` assumes Theorem 1.1.
- **Numerical weighted local bound**: `weighted_local_bound_of_deletion_principle` assumes that *every* nontrivial induced colored graph has a proper induced subgraph with no smaller exact mass. This is precisely the remaining inductive selection principle, not an unconditional proof of Lemma 2.1.

## Main unresolved work

1. **Prove the structural selection step in Lemma 2.1:** starting at a minimum-color-degree vertex, select a heavy incident color, find the slow-growth radius layer, choose a heavy independent class, and show the required proper vertex deletion works in every induced colored complete graph. The numerical and per-vertex estimates have been verified separately.
2. **Deduce Theorem 1.1** from the completed weighted local-coloring lemma, and discharge the assumption in Corollary 1.2.
3. **Complete Theorem 1.3:** integrate a compatible Lean proof of the Crittenden–Vanden Eynden covering theorem, or prove it independently. An independent formalization exists at [plby/lean-proofs, Erdős Problem 275](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos275.lean), using Lean 4.33. That repository has no declared license; its source has not been copied.
4. **Final correspondence audit:** verify the mathematical equivalence of every Lean statement to the original manuscript's hypotheses, constants, and quantifiers.

## Source modules

- `Definitions`, `Padding`, `Charge`, `ChargeClasses`, `ChargeColoring`, `ColorPaths`
- `AffineRelation`, `DifferenceCertificate`, `BezoutList`, `GcdOne`, `ArbitraryGcd`, `ResidueClass`, `ResidueNecessity`
- `DyadicLower`, `SmallCases`, `SmallThresholds`, `TwoPower`, `CoveringBridge`
- `PoweredWeights`, `SlowGrowth`, `WeightedDeletion`, `HeavyClass`, `ColorFiberMass`
- `ColorDegrees`, `ColorDeletion`, `GraphLayers`, `GraphLayerDeletion`
- `MassAccounting`, `DeletionSize`, `RealWeights`, `WeightGain`, `WeightMassInductionStep`
- `MassInduction`, `FinalWeightBound`, `WeightedLemmaReduction`, `HeavyNeighbor`, `SeedMass`
- `Audit` — `#print axioms` checks for unconditional theorems

## Build

Install [elan](https://github.com/leanprover/elan). The project pins Lean 4.28.0 and Mathlib 4.28.0:

```sh
lake update
lake exe cache get
lake build
```

GitHub Actions runs on every push and pull request. [Last green source build before the expanded audit](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44583357689): **8,066 jobs**, successful. The expanded `Audit.lean` checks are being run on the next commit. **Never infer verification of a new commit from an older green build.**

A successful `lake build` verifies the Lean propositions and their proofs. It does not certify that the propositions exactly reproduce the natural-language manuscript; the statement audit remains essential.

### Full d=1 deletion case compiled

The new `DegreeOneStar.lean`, `HeavyIndependentClass.lean`, and `DegreeOneMassStep.lean` modules complete the **d_col(v)=1 branch** of the weighted local-coloring induction (given a proper coloring of the monochromatic graph, as in the manuscript). The result constructs a strictly smaller induced subgraph whose exact real vertex-weight sum is no smaller. This was checked in [CI run 44588386054](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44588386054) (8072 jobs). The d≥2 branch and the full Lemma 2.1 are not yet verified.

## Quantitative main theorem now verified (November 19, 2026)

The full real weighted Lemma 2.1 compiled in [run 44619364740](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44619364740) and passed `#print axioms` in [run 44620242041](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44620242041). The finite difference-graph representation, signed-walk lifting, real Ramsey inequality, exact natural-number power conversion, and unconditional Corollary 1.2 all compiled in [run 44621193781](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44621193781) (8090 jobs).

The new axiom audit of `main_bound_powered` and `corollary_1_2_unconditional` is pending. **Theorem 1.3 for all r is still conditional** on the external arithmetic-progression covering theorem. See `VALIDATION.json` and `PROOF_OBLIGATIONS.md` for exact status.
