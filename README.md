# Lean formalizations — Rafael Miyazaki

Lean 4 / Mathlib repository for research formalizations in combinatorics.

## First paper

**Rafael Miyazaki, Eion Mulrenin, Cosmin Pohoată, Michael Zheng**, *Improved Ramsey Bounds for Generalized Schur Equations*, [arXiv:2605.15147](https://arxiv.org/abs/2605.15147).

The project has **successfully compiled with Lean 4.28 and Mathlib** on GitHub Actions. Its individual theorems are distinguished below; this does **not** constitute a complete formalization of the paper.

### Verified without research hypotheses

- **Lemma 3.1** (repetition/padding of solutions): `padding_lemma_3_1`.
- **Charge-count arithmetic**: `equal_charge_cross_counts` and `cross_count_le`.
- **Sufficient residue-class obstruction**: `nonzero_residue_avoids_all_lengths`.
- **Theorem 1.3, lower/optimality direction for every positive number of colors**: `two_power_lower` (a constructive recursive coloring of `[2^r-1]`).
- **Theorem 1.3, upper direction for one and two colors**: `one_color_two` and `two_color_four`.

### Compiled but conditional

- Corollary 1.2 is derived assuming `MainBoundPowered` (Theorem 1.1).
- The upper direction of Theorem 1.3 for general `r` follows from two **explicitly unproved** principles: `ResidueObstructionPrinciple` and `ResidueCoveringPrinciple`.

### Not yet proved

- Theorem 1.1, which depends on weighted local-coloring Lemma 2.1.
- The affine obstruction converse in Section 4.
- The general upper direction of Theorem 1.3.

A separate public Lean formalization of the **Crittenden–Vanden Eynden covering theorem** exists at [Erdős Problem 275](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos275.lean), in Lean 4.33. The upstream repository currently has no declared license; its code has **not** been copied or imported. Integrating its proof requires a compatible environment and appropriate licensing permission.

## Build

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake update
lake exe cache get
lake build
```

Each push and pull request triggers GitHub Actions. The status of a **particular commit** is authoritative; success on an older commit does not certify subsequent edits.

## Modules

- `Definitions.lean` — exact list-based equations and coloring propositions.
- `Padding.lean` — Lemma 3.1.
- `Charge.lean` — elementary charge-count arithmetic.
- `ResidueClass.lean` — nonzero residue-class obstruction.
- `DyadicLower.lean` — unconditional proof of the optimality half of Theorem 1.3.
- `SmallThresholds.lean` — exact two-color upper threshold.
- `SmallCases.lean` — one-color upper threshold.
- `Corollary.lean` — conditional deduction of Corollary 1.2.
- `TwoPower.lean` — conditional reduction of the remaining half of Theorem 1.3.

See [PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md) for the detailed dependency ledger.

## New arithmetic development

`AffineRelation.lean`, `DifferenceCertificate.lean`, `BezoutList.lean`, and `GcdOne.lean` form a verified chain from an integer Bézout certificate to a generalized Schur solution. In particular, if the gcd of a finite list of differences `a_i-b` is one, the finite set supports a solution. The **arbitrary-gcd case** is not yet proved; it is needed to finish the full affine residue characterization.

`RMFormal/Schur/Audit.lean` prints Lean axioms associated with the unconditional results.

**Latest verified axiom audit:** [GitHub Actions run 44524172688](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44524172688). Eight unconditional theorems reported only Lean's standard foundational axioms and no `sorryAx`.

## Affine-residue classification completed

`ResidueNecessity.lean` proves that every finite positive set avoiding all lengths of generalized Schur solutions lies in a nonzero residue class, including singletons and the empty class. The converse is proved in `ResidueClass.lean`. A direct iff theorem, `bounded_set_no_solutions_iff_residue`, **compiled successfully** in Lean 4.28.

`CoveringBridge.lean` states the classical Crittenden–Vanden Eynden covering theorem explicitly and gives a **conditional** deduction of the upper half of Theorem 1.3 from this external theorem alone. The theorem's own proof has not been imported; its formal statement is not a proof of it.

**Current complete source build:** [GitHub Actions run 44532837172](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44532837172), 8044 jobs passed. The built-in axiom audit covered 12 unconditional theorems; each reported only standard foundational axioms. The complete affine-residue classification is proved. Theorem 1.1 and the general unconditional upper direction of Theorem 1.3 are not.

## Section 3: complete local charge-coloring argument

The following three new modules are **compiled** in [GitHub Actions run 44541329817](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44541329817):

- `ChargeClasses.lean`: two short representations with identical charge cannot be adjacent by an edge of the same color in a solution-free class.
- `ChargeColoring.lean`: construct an explicit proper `Fin (2*m+1)`-coloring of any set whose vertices admit short signed representations.
- `ColorPaths.lean`: every graph walk of length at most `m` yields the needed signed representation, so the radius-`m` ball is `(2*m+1)`-colorable.

The color path is represented inductively and may repeat vertices. The local coloring uses the difference graph on natural numbers, which contains all graph walks in the complete graph on the finite interval. The central weighted local-coloring Lemma 2.1 and the full quantitative Theorem 1.1 are **not** yet proved.

## First weighted-lemma arithmetic component

`PoweredWeights.lean` formalizes the mth power of the vertex weight `W(d)=1/(χ^(d*m)*d!)` over `ℚ`, and proves the exact update identity `W(d-1)=χ^m*d*W(d)` for positive χ,d. Its proof compiled in [GitHub Actions run 44542819201](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44542819201). This is *not* a proof of the weighted local-coloring lemma; the graph-theoretic induction remains unformalized.

**Latest full verification and audit:** [GitHub Actions run 44543476720](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44543476720), 8048 jobs passed. Seventeen unconditional theorems audited with `#print axioms`; none reports `sorryAx`. The only reported axioms are `propext`, `Quot.sound`, and `Classical.choice`.
