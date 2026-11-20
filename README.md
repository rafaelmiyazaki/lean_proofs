# Lean formalizations — Rafael Miyazaki

Lean 4 / Mathlib formalizations, beginning with Miyazaki, Mulrenin, Pohoată and Zheng,
[*Improved Ramsey Bounds for Generalized Schur Equations*](https://arxiv.org/abs/2605.15147) (arXiv:2605.15147v1).

**Current status (20 November 2026): All principal stated results of this paper have independently compiled Lean proofs and clean proof-dependency audits. A final comparison of the precise Lean statements with the manuscript remains outstanding.** The pull request deliberately remains a draft until that correspondence review is completed.

## Verified principal results

| Manuscript result | Lean declaration | Verification |
|---|---|---|
| Lemma 2.1 (weighted local coloring) | `SchurFormal.weighted_local_coloring_lemma` | Successful build and clean axiom audit |
| Theorem 1.1 (quantitative bound) | `SchurFormal.main_bound_powered : MainBoundPowered` | Successful build and clean axiom audit |
| Corollary 1.2 | `SchurFormal.corollary_1_2_unconditional` | Successful build and clean axiom audit |
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

See [PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md) for the theorem-level ledger and [VALIDATION.json](VALIDATION.json) for machine-readable status.

**Draft pull request:** [#1](https://github.com/rafaelmiyazaki/lean_proofs/pull/1).
