# Lean formalizations — Rafael Miyazaki

Lean 4 / Mathlib repository for research formalization in combinatorics.

## Initial paper

**Rafael Miyazaki, Eion Mulrenin, Cosmin Pohoată, Michael Zheng**, *Improved Ramsey Bounds for Generalized Schur Equations*, [arXiv:2605.15147](https://arxiv.org/abs/2605.15147).

This branch contains formal theorem **statements**, mathematical definitions and **candidate proof scripts** for foundational lemmas. The main research results remain unproved, and some reductions use explicit unproved hypotheses. See [PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md).

### Trust status

The source was generated without a local Lean compiler. **Do not call any result machine-verified until GitHub CI's `lake build` succeeds.** Compilation, even if successful, does **not** establish that the paper's main results are proved.

### Building

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake update
lake exe cache get
lake build
```

GitHub Actions triggers a build on each push and pull request.

### Project structure

- `RMFormal/Schur/Definitions.lean`: generalized Schur equations, finite intervals and coloring propositions.
- `RMFormal/Schur/Padding.lean`: repetition/padding lemma, draft proof.
- `RMFormal/Schur/Charge.lean`: arithmetic of charged representations, draft proof.
- `RMFormal/Schur/ResidueClass.lean`: sufficient residue obstruction, draft proof.
- `RMFormal/Schur/Corollary.lean`: logical reduction of Corollary 1.2 from Theorem 1.1.
- `RMFormal/Schur/TwoPower.lean`: logical reduction of half of Theorem 1.3.
- `RMFormal/Schur/SmallCases.lean`: elementary example.
- `PROOF_OBLIGATIONS.md`: remaining mathematical work.

The intent is to turn this draft into a completely compiled repository, then formally prove the difficult mathematical inputs one by one.
