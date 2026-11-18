# Lean formalizations — Rafael Miyazaki

This repository collects Lean 4 formalizations of results in combinatorics and number theory.

Initial project: **Improved Ramsey Bounds for Generalized Schur Equations** (Miyazaki, Mulrenin, Pohoată, Zheng; arXiv:2605.15147).

**Verification warning:** The current source is a draft and has not been compiled against Lean/Mathlib. It does not prove the paper's main theorems. See `PROOF_OBLIGATIONS.md` for the outstanding dependencies.

To check the project, run `lake update`, `lake exe cache get`, and `lake build`. GitHub Actions also runs a Lean build on each push.
