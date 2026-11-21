import RMFormal.Schur.LambertFinset

/-!
# Classical Lambert length bound for a primitive indexed sequence

For a primitive zero-sum sequence of k≥2 integers, every term is
nonzero, and the sum of any nonempty proper subcollection of indexed
terms is nonzero. If all terms lie in [-b,a], with a,b positive,
then k≤a+b.

Indices retain multiplicity even when values coincide.
-/

namespace SchurFormal

theorem lambert_minimal_zero_sum_length
    {k : ℕ} (f : Fin k → ℤ)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hk : 1 < k)
    (hprimitive : PrimitiveZeroSum f)
    (hbounds : ∀ i : Fin k,
      -(b : ℤ) ≤ f i ∧ f i ≤ (a : ℤ)) :
    k ≤ a + b := by
  classical
  have hnonzero (i : Fin k) (hi : i ∈ (Finset.univ : Finset (Fin k))) :
      f i ≠ 0 := primitive_zero_sum_term_ne_zero hk f hprimitive i
  have hprim' (t : Finset (Fin k)) (ht : t.Nonempty)
      (_hsub : t ⊆ Finset.univ) (hproper : t ≠ Finset.univ) :
      (∑ i ∈ t, f i) ≠ 0 := hprimitive.2 t ht hproper
  have hlen := lambert_length_of_primitive_finset
    (Finset.univ : Finset (Fin k)) f a b ha hb
    (by simpa using hprimitive.1)
    hnonzero (by intro i _; exact hbounds i) hprim'
  simpa using hlen

end SchurFormal
