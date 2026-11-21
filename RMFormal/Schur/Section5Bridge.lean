import RMFormal.Schur.ResidueRootProduct

/-!
# Section 5: exact outstanding quantitative principle

Theorem 1.3 already proves existence of a Schur equation for some
positive m. Section 5 strengthens this to m < 2^r.

The only new set-theoretic input is the following bounded version
of the residue obstruction: a subset of [M] avoiding all positive
equation lengths m < M lies in a nonzero residue class.

This module proves the exact reduction from that NEW principle to
the stronger multicolor theorem. The principle is an explicit
hypothesis, NOT an axiom or a theorem proved in this file.
-/

namespace SchurFormal

/-- The sole new set-level statement needed for the Section 5
short-length refinement. This is a *proposition*, not a proof. -/
def BoundedResidueObstruction : Prop :=
  ∀ M : ℕ, 1 < M →
  ∀ A : Set ℕ,
    (∀ x ∈ A, x ∈ PositiveInterval M) →
    (∀ m : ℕ, 0 < m → m < M →
      ¬ HasEquation A (m + 1) m) →
    ∃ d a : ℕ, 2 ≤ d ∧ 0 < a ∧ a < d ∧
      ∀ x ∈ A, x % d = a

/-- Section 5's strengthened upper direction, as a proposition. -/
def BoundedTwoPowerUpper : Prop :=
  ∀ r : ℕ, 0 < r → ∀ color : ℕ → Fin r,
    ∃ m : ℕ, 0 < m ∧ m < 2 ^ r ∧
      MonochromaticSolution r (2 ^ r) (m + 1) m color

/-- The precise mathematical reduction:
the bounded residue obstruction plus the independently verified
exponential covering principle implies the short-length refinement. -/
theorem bounded_two_power_upper_of_bounded_obstruction
    (hbounded : BoundedResidueObstruction) :
    BoundedTwoPowerUpper := by
  intro r hr color
  classical
  have hM : 1 < 2 ^ r := by
    obtain ⟨k, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    have hpos : 0 < 2 ^ k := by positivity
    rw [pow_succ]
    omega
  by_contra hnone
  have hAvoid (m : ℕ) (hm : 0 < m) (hmm : m < 2 ^ r) :
      ¬ MonochromaticSolution r (2 ^ r) (m + 1) m color := by
    intro hmono
    exact hnone ⟨m, hm, hmm, hmono⟩
  have hObstruction (i : Fin r) :
      ∃ d a : ℕ, 2 ≤ d ∧ 0 < a ∧ a < d ∧
        ∀ x ∈ ColorClass (2 ^ r) color i, x % d = a := by
    apply hbounded (2 ^ r) hM (ColorClass (2 ^ r) color i)
    · intro x hx
      exact hx.1
    · intro m hm hmm hsol
      exact hAvoid m hm hmm ⟨i, hsol⟩
  choose d a hparams using hObstruction
  have hparameters (i : Fin r) :
      2 ≤ d i ∧ 0 < a i ∧ a i < d i := by
    rcases hparams i with ⟨hd, ha, halt, _⟩
    exact ⟨hd, ha, halt⟩
  have hCovers (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 2 ^ r) :
      ∃ i : Fin r, n % d i = a i := by
    refine ⟨color n, ?_⟩
    exact (hparams (color n)).2.2.2 n ⟨⟨hn, hn'⟩, rfl⟩
  obtain ⟨i, hi⟩ :=
    residue_covering_from_exponential r hr d a hparameters hCovers
  have ha0 : a i = 0 := by simpa using hi.symm
  exact (Nat.ne_of_gt (hparameters i).2.1) ha0

end SchurFormal
