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


## Section 5 development (20 November 2026)

The strengthened bound `1 ≤ m ≤ 2^r - 1` is **not yet verified**. The following independent intermediate statements have passing Lean builds and clean `#print axioms` audits in [run 44826326345](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44826326345):

- `exists_minimal_schur_length` and `nonresidue_has_minimal_schur_length`: extract the least positive equation length.
- `ordered_opposite_differences_le`: the ordered-pairing estimate `a+b ≤ M`.
- `consecutive_pair_exact_minimum`: verify the sharp example `{M-1,M}`.
- `exists_lambert_greedy_step`, `exists_lambert_bounded_order` and `LambertBoundedWalk.prefix_bounds`: construct a greedy ordering with running sums in `(-b,a]`.
- `lambert_length_of_distinct_prefixes`: a pigeonhole bound `k ≤ a+b`, **conditional on prefix distinctness**.
- `bounded_two_power_upper_of_bounded_obstruction`: the multicolor refinement, **conditional on the explicit unproved** `BoundedResidueObstruction`.

The indexed primitive-zero-sum definition and nonvanishing lemma compile in [run 44826625519](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44826625519). Additional prefix-collision and primitive-sublist bridge modules are under CI, not yet recorded as verified.

**Unresolved mathematical bridge:** show that a minimum-length Schur relation yields a primitive balanced pairing; show that every nonempty proper zero-sum subcollection is excluded after any greedy ordering. Apply the already-verified length estimate and diameter bound to prove the bounded-obstruction principle unconditionally.



## November 21: the indexed Lambert theorem has been formalized

The following additional statements now have **successful source builds**:

| Step | Lean declaration | Supporting CI |
|---|---|---|
| Weighted prefix collision, preserving repeated numerical values | `weighted_zero_sublist_of_prefix_collision` | [44905537248](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44905537248) |
| Lambert inequality for primitive indexed finite zero-sum collections | `lambert_length_of_primitive_finset` | [44905537248](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44905537248) |
| Classical `Fin k` version, `k≤a+b` | `lambert_minimal_zero_sum_length` | [44905606129](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44905606129) |
| Primitive balanced pair implies primitive zero-sum differences | `primitive_balanced_pair_to_zero_sum` | [44905606129](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44905606129) |
| Lambert bound for primitive balanced pairs | `primitive_balanced_pair_length_bound` | [44905606129](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44905606129) |
| Sorted-pair diameter plus Lambert implies `m≤M-1` | `section_5_numerical_conclusion` | [44905838508](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44905838508) |

**Important remaining mathematical gap:** starting from a minimum-length `(m+1,m)` Schur solution in a positive finite set `A⊆[M]`, construct the indexed balanced pair `P,Q` after adjoining one zero to `Q`, prove that no nonempty proper balanced subidentity exists (using minimality), sort both sides with proof of preserved sums and multiplicities, and derive the signed-difference magnitude hypotheses and attained extrema. Only then can the existing numerical conclusion discharge `BoundedResidueObstruction` and make `BoundedTwoPowerUpper` unconditional.

The entire Section 5 refinement is **still not verified**, and the draft PR remains open. The expanded `Section5Audit.lean` has displayed only standard Lean axioms for the new core declarations; a missing import in that audit module was corrected in commit `81934a0`, with the corrected full build pending.
