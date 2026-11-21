# Statement-fidelity audit — Schur formalization

**Source:** [Miyazaki, Mulrenin, Pohoată, Zheng, arXiv:2605.15147v1 (HTML)](https://arxiv.org/html/2605.15147), 14 May 2026.
**Review date:** 20 November 2026.

This document compares the *types of the formal propositions*, rather than trusting their names or the natural-language comments attached to them. All declarations mentioned as verified below have passing Lean builds and standard-axiom-only dependency audits.

## Shared conventions

| Manuscript convention | Lean representation | Review |
|---|---|---|
| `[N] = {1,...,N}` | `PositiveInterval N = {x : ℕ | 1 ≤ x ∧ x ≤ N}` | Matches |
| An `r`-coloring | `color : ℕ → Fin r`; only values on `PositiveInterval N` are used | Equivalent to coloring `[N]` when `r>0` |
| Monochromatic variables | `ColorClass N color i` and `HasEquation` | Matches |
| Repeated summands allowed | `HasEquation` uses **lists**, not distinct-element sets | Matches |
| `m,r in ℕ` in the paper's positive-integer convention | Explicit `0 < m` and `0 < r` | Matches |

## Result-by-result correspondence

**Lemma 2.1.** The source assumes a `q`-local coloring of `K_n`, radius-`ell` monochromatic balls with chromatic number at most `chi`, and `chi ≥ 2`; the conclusion is `n ≤ chi^q (q!)^(1/ell)`. `weighted_local_coloring_lemma` has the same inequality and the same structural requirements, expressing chromatic number at most `chi` as existence of a proper map to `Fin chi`. Its finite vertex and color types cover the finite-graph case. **Matches the named lemma.**

**Theorem 1.1.** The source states that if an `r`-coloring avoids the `(m+1,m)` equation, then `N ≤ (2m+1)^r (r!)^(1/m)`. `main_bound_powered : MainBoundPowered` proves the equivalent integer-powered inequality
`N^m ≤ (2m+1)^(r*m) * r!` under `m,r>0`. The equivalence uses the monotonicity of positive real `m`-th powers. **Matches the quantitative statement.**

**Corollary 1.2.** The source takes `a>b>0`, `d=a-b`, `b=dm+w`, `0≤w<d`, and `m≥1` (equivalently `a≤2b`). The existing `corollary_1_2_unconditional` is formulated with explicit `d,m,w`, even allowing arbitrary `w≥0`, which is slightly stronger. The additional **verified** `corollary_1_2_source_parameters` starts instead with `b<a`, `a≤2*b`, and defines `m=b/(a-b)`, proving the same powered inequality. This removes the need to accept a manual Euclidean-division substitution. **Matches the source corollary.**

**Theorem 1.3.** The source asserts that every `r`-coloring of `[2^r]` has a monochromatic solution for some `m≥1` and that `2^r` is optimal. `TwoPowerUpper` gives the universal coloring statement with `m>0`; `TwoPowerLower` constructs a coloring of `[2^r-1]` avoiding solutions for every `m>0`. Their conjunction, `theorem_1_3_unconditional`, proves the sharp threshold. **Matches both directions of the stated theorem.**

**Lemma 3.1.** The padding result uses a set containing a solution and repeats both sides `t` times before adding `w` shared terms. `padding_lemma_3_1` allows even `t=0` (with nonempty `A` ensured by a positive left length), a harmless strengthening over the source's `t≥1`. **Matches the source's applicable domain.**

## Kernel/trust audit

- [Main theorem and corollary audit](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44621910477)
- [Theorem 1.3 combined proof and axiom audit](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44746726788)
- [Source-parameter Corollary 1.2 build and axiom audit](https://github.com/rafaelmiyazaki/lean_proofs/actions/runs/44748112697)

The final declarations reported only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`, not `sorryAx`. The general externally cited Crittenden–Vanden Eynden theorem was *not* silently assumed: its specialized residue-covering consequence was proved from a sparse exponential-product argument.

## Scope limits and remaining work

This is a **preliminary source-to-statement audit** of the major named results, not an independent second formal verification of the entire manuscript. It does not yet establish formal versions of every supplementary observation:

1. Remark 2.2: the corresponding numerical improvement for odd-cycle Ramsey numbers.
2. Section 5: the quantitative strengthening `1 ≤ m ≤ 2^r - 1`. The current Theorem 1.3 proves `∃ m>0`, **without** this upper bound.
3. Section 5: the logarithmic `m_0` estimate in the regime of large `[b^r]`.
4. The full Crittenden–Vanden Eynden integer-covering theorem (Theorem 4.1) is an externally cited input in the manuscript, not a novel assertion of the paper. Its required specialized consequence has been independently verified here.

The repository's draft status should remain until an independent mathematical reviewer checks the statement correspondence and decides which additional claims should be inside the scope of a *complete-paper* formalization.


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
