# Lean formalizations — Rafael Miyazaki

Lean 4 / Mathlib formalizations, beginning with Miyazaki, Mulrenin, Pohoată and Zheng,
[*Improved Ramsey Bounds for Generalized Schur Equations*](https://arxiv.org/abs/2605.15147) (arXiv:2605.15147v1).

**Current status (20 November 2026): All principal stated results of this paper have independently compiled Lean proofs and clean proof-dependency audits. A final comparison of the precise Lean statements with the manuscript remains outstanding.** The pull request deliberately remains a draft until that correspondence review is completed.

## Verified principal results

| Manuscript result | Lean declaration | Verification |
|---|---|---|
| Lemma 2.1 (weighted local coloring) | `SchurFormal.weighted_local_coloring_lemma` | Successful build and clean axiom audit |
| Theorem 1.1 (quantitative bound) | `SchurFormal.main_bound_powered : MainBoundPowered` | Successful build and clean axiom audit |
| Corollary 1.2 (quotient parameters) | `SchurFormal.corollary_1_2_unconditional` | Successful build and clean axiom audit |
| Corollary 1.2 (original a,b hypotheses) | `SchurFormal.corollary_1_2_source_parameters` | Successful build and clean axiom audit |
| Theorem 1.3, lower/optimality | `SchurFormal.two_power_lower : TwoPowerLower` | Successful build and clean axiom audit |
| Theorem 1.3, general upper | `SchurFormal.two_power_upper_unconditional : TwoPowerUpper` | Successful build and clean axiom audit |
| Theorem 1.3, both directions | `SchurFormal.theorem_1_3_unconditional` | Successful build and clean axiom audit |

**Current complete build and audit:** [GitHub Actions 44746726788](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44746726788). The final theorem's `#print axioms` output contains only `propext`, `Classical.choice`, and `Quot.sound`, and **no `sorryAx`**.

## Independent proof of the final arithmetic-covering step

The proof of general Theorem 1.3 does **not** rely on an unproved Crittenden–Vanden Eynden assumption.

- `ExponentialRecurrence.lean` verifies that an exponential sum of `k` terms vanishing on `k` consecutive indices vanishes at all subsequent indices.
- `ProductExponential.lean` expands a product of `r` geometric differences into `2^r` exponential terms.
- `ResidueRootProduct.lean` uses primitive complex roots of unity to encode residue classes and proves `residue_covering_from_exponential : ResidueCoveringPrinciple`. The modulus-product argument gives the contradiction needed for the Schur upper bound.
- `Theorem13.lean` packages the upper and lower directions and audits all final declarations.

The repository retains `CVECoveringStatement` as an *unproved proposition* in the older conditional bridge. The **full general integer interval-covering theorem is not claimed to have been formalized**; the precise specialized principle needed for Theorem 1.3 has instead been proved outright. No external unlicensed code was copied.

## Verification and trust boundaries

These proofs have no `sorry` placeholders or project-specific axioms in the audited final theorem dependencies. Lean checks the theorem statements actually declared in the source, not automatically their equivalence to a natural-language manuscript. The remaining audit must compare equations, repetitions of terms, interval conventions, colors, positivity, every quantified hypothesis, and constants with arXiv:2605.15147v1.

## Build

This repository pins Lean 4.28.0 and Mathlib 4.28.0.

```sh
lake update
lake exe cache get
lake build
```

See [STATEMENT_FIDELITY.md](STATEMENT_FIDELITY.md) for a claim-by-claim manuscript comparison. The Section 5 quantitative refinements and the odd-cycle estimate in Remark 2.2 are not separately formalized. See [PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md) for the theorem-level ledger and [VALIDATION.json](VALIDATION.json) for machine-readable status.

**Draft pull request:** [#1](https://github.com/rafaelmiyazaki/lean_proofs/pull/1).

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
