# Proof-obligation ledger

**Paper:** Miyazaki, Mulrenin, Pohoată and Zheng, [*Improved Ramsey Bounds for Generalized Schur Equations*](https://arxiv.org/abs/2605.15147), arXiv:2605.15147v1.

**Last verified source date:** 2026-11-20.

## Principal result verification

| Mathematical result | Declaration | Status |
|---|---|---|
| Lemma 3.1, padding | `padding_lemma_3_1` | Unconditional, audited |
| Affine-residue obstruction characterization | `bounded_set_no_solutions_iff_residue` | Unconditional, audited |
| Lemma 2.1, weighted local-coloring | `weighted_local_coloring_lemma` | Unconditional, audited |
| Theorem 1.1, exact natural-number power bound | `main_bound_powered` | Unconditional, audited |
| Corollary 1.2 (quotient form) | `corollary_1_2_unconditional` | Unconditional, audited |
| Corollary 1.2 (original a,b variables) | `corollary_1_2_source_parameters` | Unconditional, audited |
| Theorem 1.3, optimality/lower direction | `two_power_lower` | Unconditional, audited |
| Theorem 1.3, general upper direction | `two_power_upper_unconditional` | Unconditional, audited |
| Theorem 1.3, both directions | `theorem_1_3_unconditional` | Unconditional, audited |

Every theorem above is in namespace `SchurFormal`.

## Main proof architecture

- **Generalized Schur setup:** `Definitions`, `Padding`, `AffineRelation`, `DifferenceCertificate`, `BezoutList`, `GcdOne`, `ArbitraryGcd`, `ResidueClass`, `ResidueNecessity`.
- **Weighted graph lemma:** `PoweredWeights`, `SlowGrowth`, `WeightedDeletion`, `HeavyClass`, `GraphLayers`, `MassAccounting`, `RealWeights`, `DegreeOneMassStep`, `DegreeGeTwoMassStep`, `AllCasesDeletion`, `UniversalWeightedInduction`, `WeightedLemma21` and their supporting imports.
- **Quantitative main theorem:** `FiniteDifferenceGraph`, `FiniteDifferenceWalk`, `FiniteSchurRealBound`, `SchurPowerConversion`, `MainTheorem11`, `Corollary12`.
- **Theorem 1.3 lower direction:** `DyadicLower` and `SmallCases`.
- **New independent upper-direction proof:** `ExponentialRecurrence`, `ProductExponential`, `ResidueRootProduct`, `Theorem13`.

## The final covering step

The older `CoveringBridge.lean` states the classical Crittenden–Vanden Eynden covering theorem as `CVECoveringStatement : Prop` and proves only a *conditional* consequence. That statement is **not** treated as an axiom and is **not** used by the new unconditional Theorem 1.3 proof.

Instead, `ResidueRootProduct.lean` proves `residue_covering_from_exponential : ResidueCoveringPrinciple` independently. For each residue condition `n % d_i = a_i`, a primitive `d_i`-th complex root `ζ_i` represents it as `ζ_i^n = ζ_i^{a_i}`. A product of the resulting `r` differences is a `2^r`-term exponential sum. Consecutive-zero propagation forces it to vanish at the positive product of the moduli. Since this product has residue zero modulo every modulus, a covered nonzero residue class is impossible.

This proves the **specialized residue-covering consequence required by the paper**, not the general integer covering theorem in all its formulations. The external third-party formalization was neither imported nor copied.

## Kernel and dependency verification

- [Run 44620242041](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44620242041): weighted Lemma 2.1 axiom audit.
- [Run 44621910477](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44621910477): Theorem 1.1 and Corollary 1.2 axiom audit.
- [Run 44744789787](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44744789787): `ProductExponential` compilation.
- [Run 44746452616](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44746452616): unconditional residue-covering and general upper bound compilation.
- [Run 44746726788](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44746726788): complete Theorem 1.3 compilation and axiom audit.

The last run reports `[propext, Classical.choice, Quot.sound]` for `theorem_1_3_unconditional`, `two_power_upper_unconditional`, `residue_covering_from_exponential`, and `primitive_root_pow_eq_iff_mod`; it does **not** report `sorryAx`.

## Source-parameter Corollary 1.2

The theorem `corollary_1_2_source_parameters` uses the manuscript's original hypotheses `a > b` and `a ≤ 2*b`, defines `m = b / (a-b)`, and proves the exact powered version of Corollary 1.2. [Successful compilation and axiom audit 44748112697](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44748112697) reports only standard Lean axioms.

## Additional manuscript claims still outside current formal scope

- **Remark 2.2:** odd-cycle multicolor Ramsey-number estimate derived from Lemma 2.1.
- **Section 5:** the improved choice `1 ≤ m ≤ 2^r - 1`, proved via minimal zero-sum sequences and Lambert's theorem.
- **Section 5:** a further large-interval / small-equation-length logarithmic estimate.
- **Theorem 4.1:** the general Crittenden–Vanden Eynden progression-covering statement is cited from the literature. The specialized consequence actually used in Theorem 1.3 is now formally proved independently.

See `STATEMENT_FIDELITY.md` for the source-to-Lean comparison.

## Outstanding non-kernel audit

A final mathematical statement-fidelity review against the complete manuscript remains: repeated summands, ranges `[N]`, all colors and equation quantifiers, variable positivity, constants and exact theorem/corollary correspondence. Only after this review should the draft pull request be considered complete as a formalization *of the paper*, rather than simply a collection of verified Lean propositions.
