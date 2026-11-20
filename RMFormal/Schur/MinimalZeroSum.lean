import RMFormal.Schur.LambertLength

/-!
# Minimal zero-sum sequences over the integers

A family indexed by Fin k is primitive if its entire sum is zero
but no nonempty proper subfamily sums to zero. This definition is
multiplicity-sensitive: equal integer values at distinct indices
remain separate terms.

For k≥2, primitivity forces every term to be nonzero. The next step
is to deduce pairwise distinct proper-prefix sums after the bounded
greedy reordering, completing Lambert's length inequality.
-/

namespace SchurFormal

/-- A primitive zero-sum family. The full index set sums to zero,
and no proper nonempty subset of indices has sum zero. -/
def PrimitiveZeroSum {k : ℕ} (f : Fin k → ℤ) : Prop :=
  (∑ i : Fin k, f i) = 0 ∧
    ∀ s : Finset (Fin k), s.Nonempty →
      s ≠ Finset.univ → (∑ i ∈ s, f i) ≠ 0

/-- For a primitive zero-sum family with at least two entries,
every individual term is nonzero. -/
theorem primitive_zero_sum_term_ne_zero
    {k : ℕ} (hk : 1 < k) (f : Fin k → ℤ)
    (hprim : PrimitiveZeroSum f) (i : Fin k) :
    f i ≠ 0 := by
  have hproper : ({i} : Finset (Fin k)) ≠ Finset.univ := by
    intro heq
    have hc := congrArg Finset.card heq
    simp at hc
    omega
  have hsingle : (∑ j ∈ ({i} : Finset (Fin k)), f j) ≠ 0 :=
    hprim.2 {i} (by simp) hproper
  simpa using hsingle

end SchurFormal
