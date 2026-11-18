import Mathlib

/-!
# Basic objects for generalized Schur equations

Reference: Miyazaki--Mulrenin--Pohoata--Zheng,
"Improved Ramsey bounds for generalized Schur equations", arXiv:2605.15147.

Lists (not sets) encode solutions: repeated terms are allowed.
The interval [N] means {1,...,N}, including 1 and excluding 0.
-/

namespace SchurFormal

/-- A solution to `x₁+⋯+x_a = y₁+⋯+y_b` with all terms in `A`.
    The entries need not be distinct. -/
def HasEquation (A : Set ℕ) (a b : ℕ) : Prop :=
  ∃ xs ys : List ℕ,
    xs.length = a ∧
    ys.length = b ∧
    (∀ x ∈ xs, x ∈ A) ∧
    (∀ y ∈ ys, y ∈ A) ∧
    xs.sum = ys.sum

/-- The positive integer interval `[N]`. -/
def PositiveInterval (N : ℕ) : Set ℕ :=
  {x | 1 ≤ x ∧ x ≤ N}

/-- A color class inside `[N]` for an `r`-coloring. -/
def ColorClass {r : ℕ} (N : ℕ) (color : ℕ → Fin r)
    (i : Fin r) : Set ℕ :=
  {x | x ∈ PositiveInterval N ∧ color x = i}

/-- The existence of a monochromatic `(a,b)` sum equation. -/
def MonochromaticSolution (r N a b : ℕ)
    (color : ℕ → Fin r) : Prop :=
  ∃ i : Fin r, HasEquation (ColorClass N color i) a b

/-- Power-form conjecture to formalize (Theorem 1.1);
    this is a proposition, not a proof. -/
def MainBoundPowered : Prop :=
  ∀ m r N : ℕ, 0 < m → 0 < r →
    ∀ color : ℕ → Fin r,
      (∀ i : Fin r,
        ¬ HasEquation (ColorClass N color i) (m + 1) m) →
      N ^ m ≤ (2 * m + 1) ^ (r * m) * Nat.factorial r

/-- Upper half of Theorem 1.3; not proved unconditionally. -/
def TwoPowerUpper : Prop :=
  ∀ r : ℕ, 0 < r → ∀ color : ℕ → Fin r,
    ∃ m : ℕ, 0 < m ∧
      MonochromaticSolution r (2 ^ r) (m + 1) m color

/-- Optimality half of Theorem 1.3; not yet proved. -/
def TwoPowerLower : Prop :=
  ∀ r : ℕ, 0 < r → ∃ color : ℕ → Fin r,
    ∀ m : ℕ, 0 < m →
      ¬ MonochromaticSolution r (2 ^ r - 1) (m + 1) m color

end SchurFormal
