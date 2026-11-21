import RMFormal.Schur.Theorem13

/-!
# Section 5: ordered difference diameter and minimal witnesses

The quantitative proof first chooses a shortest Schur solution,
adds a zero to its shorter side, sorts the resulting equal-sized
multisets, and studies their pairwise differences.

The elementary, but essential, last estimate is formalized below:
if 0 ≤ p₁ ≤ ... ≤ pₖ ≤ M and 0 ≤ q₁ ≤ ... ≤ qₖ ≤ M,
then the diameter of the paired differences pᵢ - qᵢ is at most M.

This file is not a proof of the Section 5 bound: the independent
minimal zero-sum (Lambert) inequality k ≤ a+b is still required.
-/

namespace SchurFormal

/-- Any nonempty collection of generalized Schur solutions contains
a solution with minimum positive right-hand length. -/
theorem exists_minimal_schur_length
    (A : Set ℕ)
    (hexists : ∃ m : ℕ, 0 < m ∧ HasEquation A (m + 1) m) :
    ∃ m : ℕ, 0 < m ∧ HasEquation A (m + 1) m ∧
      ∀ t : ℕ, 0 < t → t < m →
        ¬ HasEquation A (t + 1) t := by
  classical
  let P : ℕ → Prop := fun m => 0 < m ∧ HasEquation A (m + 1) m
  have hex : ∃ m, P m := hexists
  refine ⟨Nat.find hex, (Nat.find_spec hex).1,
    (Nat.find_spec hex).2, ?_⟩
  intro t ht hlt hsol
  have hmin : Nat.find hex ≤ t := Nat.find_min' hex ⟨ht, hsol⟩
  omega

/-- The diameter of differences of two increasing integer sequences
in [0,M] does not exceed M. No assumption on the sum is needed. -/
theorem ordered_difference_diameter_le
    {k M : ℕ} (p q : Fin k → ℕ)
    (hP : ∀ i j : Fin k, i ≤ j → p i ≤ p j)
    (hQ : ∀ i j : Fin k, i ≤ j → q i ≤ q j)
    (hpM : ∀ i : Fin k, p i ≤ M)
    (hqM : ∀ i : Fin k, q i ≤ M)
    (i j : Fin k) :
    (p i : ℤ) - (q i : ℤ) -
      ((p j : ℤ) - (q j : ℤ)) ≤ (M : ℤ) := by
  rcases le_total i j with hij | hji
  · have hpi := hP i j hij
    have hqj := hqM j
    omega
  · have hqji := hQ j i hji
    have hpi := hpM i
    omega

/-- If a positive difference a and a negative difference -b
occur in the ordered pairing, their magnitudes satisfy a+b ≤ M. -/
theorem ordered_opposite_differences_le
    {k M : ℕ} (p q : Fin k → ℕ)
    (hP : ∀ i j : Fin k, i ≤ j → p i ≤ p j)
    (hQ : ∀ i j : Fin k, i ≤ j → q i ≤ q j)
    (hpM : ∀ i : Fin k, p i ≤ M)
    (hqM : ∀ i : Fin k, q i ≤ M)
    (i j : Fin k) (a b : ℕ)
    (ha : (p i : ℤ) - (q i : ℤ) = (a : ℤ))
    (hb : (p j : ℤ) - (q j : ℤ) = -(b : ℤ)) :
    a + b ≤ M := by
  have h := ordered_difference_diameter_le
    p q hP hQ hpM hqM i j
  omega

/-- The existing affine-residue characterization guarantees that
every finite positive set with no nonzero residue obstruction has a
Schur solution of *minimum* positive length. This is the exact
starting point of the Section 5 quantitative argument. -/
theorem nonresidue_has_minimal_schur_length
    (A : Set ℕ) (M : ℕ)
    (hA : ∀ x ∈ A, x ∈ PositiveInterval M)
    (hnot : ¬ ∃ d a : ℕ, 2 ≤ d ∧ 0 < a ∧ a < d ∧
      ∀ x ∈ A, x % d = a) :
    ∃ m : ℕ, 0 < m ∧ HasEquation A (m + 1) m ∧
      ∀ t : ℕ, 0 < t → t < m →
        ¬ HasEquation A (t + 1) t := by
  classical
  apply exists_minimal_schur_length A
  by_contra hnone
  apply hnot
  apply (bounded_set_no_solutions_iff_residue A M hA).mp
  intro m hm hsol
  exact hnone ⟨m, hm, hsol⟩

#print axioms nonresidue_has_minimal_schur_length

end SchurFormal
