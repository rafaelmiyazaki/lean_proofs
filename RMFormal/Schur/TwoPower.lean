import RMFormal.Schur.Definitions
import RMFormal.Schur.ResidueClass

/-!
# Theorem 1.3 upper bound conditional on two major mathematical principles

The principle hypotheses are explicit and MUST NOT be treated as
unconditional proofs of the main research theorem.
-/

namespace SchurFormal

/-- Difficult direction of the affine obstruction; still unproved. -/
def ResidueObstructionPrinciple : Prop :=
  ∀ N : ℕ, ∀ A : Set ℕ,
    (∀ x ∈ A, x ∈ PositiveInterval N) →
    (∀ m : ℕ, 0 < m → ¬ HasEquation A (m + 1) m) →
    ∃ d a : ℕ, 2 ≤ d ∧ 0 < a ∧ a < d ∧
      ∀ x ∈ A, x % d = a

/-- Consequence of the Crittenden--Vanden Eynden covering theorem.
    Still unproved in this project. -/
def ResidueCoveringPrinciple : Prop :=
  ∀ k : ℕ, 0 < k →
    ∀ d a : Fin k → ℕ,
      (∀ i, 2 ≤ d i ∧ 0 < a i ∧ a i < d i) →
      (∀ n : ℕ, 1 ≤ n → n ≤ 2 ^ k →
        ∃ i : Fin k, n % d i = a i) →
      ∃ i : Fin k, 0 % d i = a i

/-- Reduction of the upper half of Theorem 1.3 to the two
    independent, currently unproved principles above. -/
theorem two_power_upper_of_principles
    (hob : ResidueObstructionPrinciple)
    (hcover : ResidueCoveringPrinciple) : TwoPowerUpper := by
  intro r hr color
  classical
  by_contra hnone
  have hAvoid (m : ℕ) (hm : 0 < m) :
      ¬ MonochromaticSolution r (2 ^ r) (m + 1) m color := by
    intro hmono
    exact hnone ⟨m, hm, hmono⟩
  have hObstruction (i : Fin r) :
      ∃ d a : ℕ, 2 ≤ d ∧ 0 < a ∧ a < d ∧
        ∀ x ∈ ColorClass (2 ^ r) color i, x % d = a := by
    apply hob (2 ^ r) (ColorClass (2 ^ r) color i)
    · intro x hx
      exact hx.1
    intro m hm hsol
    exact hAvoid m hm ⟨i, hsol⟩
  choose d a hparams using hObstruction
  have hparameters (i : Fin r) :
      2 ≤ d i ∧ 0 < a i ∧ a i < d i := by
    rcases hparams i with ⟨hd, ha, halt, _⟩
    exact ⟨hd, ha, halt⟩
  have hCovers (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 2 ^ r) :
      ∃ i : Fin r, n % d i = a i := by
    refine ⟨color n, ?_⟩
    exact (hparams (color n)).2.2.2 n ⟨⟨hn, hn'⟩, rfl⟩
  obtain ⟨i, hi⟩ := hcover r hr d a hparameters hCovers
  have ha0 : a i = 0 := by simpa using hi.symm
  exact (Nat.ne_of_gt (hparameters i).2.1) ha0

end SchurFormal
