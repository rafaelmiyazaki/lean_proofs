import RMFormal.Schur.LambertTheorem

/-!
# Section 5: balanced multiset identities give minimal zero-sum sequences

Equal-sized multisets are represented by functions on Fin k.
The two functions may repeat values, but each index is a separate
occurrence. A balanced identity is primitive precisely when no
nonempty proper subset of positions has equal partial sums.

This is the formal bridge from primitive balanced pairs to
Lambert's indexed minimal zero-sum condition.
-/

namespace SchurFormal

/-- If no nonempty proper subcollection of a balanced pair has
equal sums, its termwise difference is a primitive zero-sum sequence. -/
theorem primitive_balanced_pair_to_zero_sum
    {k : ℕ} (p q : Fin k → ℕ)
    (hBalance : (∑ i : Fin k, p i) = ∑ i : Fin k, q i)
    (hPrimitiveBalanced :
      ∀ s : Finset (Fin k), s.Nonempty → s ≠ Finset.univ →
        (∑ i ∈ s, p i) ≠ ∑ i ∈ s, q i) :
    PrimitiveZeroSum (fun i => (p i : ℤ) - (q i : ℤ)) := by
  constructor
  · simp only [Finset.sum_sub_distrib]
    have hInt : (∑ i : Fin k, (p i : ℤ)) =
        (∑ i : Fin k, (q i : ℤ)) := by
      exact_mod_cast hBalance
    exact sub_eq_zero.mpr hInt
  · intro s hs hproper
    intro hzero
    have hEqInt :
        (∑ i ∈ s, (p i : ℤ)) = (∑ i ∈ s, (q i : ℤ)) := by
      have hh : (∑ i ∈ s, (p i : ℤ)) -
          (∑ i ∈ s, (q i : ℤ)) = 0 := by
        simpa only [Finset.sum_sub_distrib] using hzero
      exact sub_eq_zero.mp hh
    have hEqNat :
        (∑ i ∈ s, p i) = (∑ i ∈ s, q i) := by
      exact_mod_cast hEqInt
    exact hPrimitiveBalanced s hs hproper hEqNat

/-- The Lambert bound for a primitive balanced pair, with the
positive/negative magnitude bounds given explicitly. -/
theorem primitive_balanced_pair_length_bound
    {k : ℕ} (p q : Fin k → ℕ)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hk : 1 < k)
    (hBalance : (∑ i : Fin k, p i) = ∑ i : Fin k, q i)
    (hPrimitiveBalanced :
      ∀ s : Finset (Fin k), s.Nonempty → s ≠ Finset.univ →
        (∑ i ∈ s, p i) ≠ ∑ i ∈ s, q i)
    (hBounds : ∀ i : Fin k,
      -(b : ℤ) ≤ (p i : ℤ) - (q i : ℤ) ∧
        (p i : ℤ) - (q i : ℤ) ≤ (a : ℤ)) :
    k ≤ a + b := by
  exact lambert_minimal_zero_sum_length
    (fun i => (p i : ℤ) - (q i : ℤ))
    a b ha hb hk
    (primitive_balanced_pair_to_zero_sum p q hBalance hPrimitiveBalanced)
    hBounds

end SchurFormal
