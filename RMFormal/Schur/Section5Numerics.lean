import RMFormal.Schur.BalancedPrimitive
import RMFormal.Schur.Section5Diameter

/-!
# Section 5: package the entire numerical deduction

Given a primitive balanced pair of sorted equal-size multisets in
[0,M], apply the independently formalized Lambert length estimate
and the ordered-difference diameter estimate to obtain m≤M-1,
where the common multiset cardinality is m+1.

This isolates the remaining source-to-formalization task: construct
the primitive sorted balanced pair from a minimum-length Schur
solution. No such construction is assumed to have been proved here.
-/

namespace SchurFormal

theorem section_5_numerical_conclusion
    (m M a b : ℕ) (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    (p q : Fin (m + 1) → ℕ)
    (hP : ∀ i j : Fin (m + 1), i ≤ j → p i ≤ p j)
    (hQ : ∀ i j : Fin (m + 1), i ≤ j → q i ≤ q j)
    (hpM : ∀ i : Fin (m + 1), p i ≤ M)
    (hqM : ∀ i : Fin (m + 1), q i ≤ M)
    (hBalance : (∑ i : Fin (m + 1), p i) =
      ∑ i : Fin (m + 1), q i)
    (hPrimitiveBalanced :
      ∀ s : Finset (Fin (m + 1)), s.Nonempty → s ≠ Finset.univ →
        (∑ i ∈ s, p i) ≠ ∑ i ∈ s, q i)
    (hBounds : ∀ i : Fin (m + 1),
      -(b : ℤ) ≤ (p i : ℤ) - (q i : ℤ) ∧
        (p i : ℤ) - (q i : ℤ) ≤ (a : ℤ))
    (i j : Fin (m + 1))
    (hMax : (p i : ℤ) - (q i : ℤ) = (a : ℤ))
    (hMin : (p j : ℤ) - (q j : ℤ) = -(b : ℤ)) :
    m ≤ M - 1 := by
  have hk : 1 < m + 1 := by omega
  have hLambert : m + 1 ≤ a + b :=
    primitive_balanced_pair_length_bound
      p q a b ha hb hk hBalance hPrimitiveBalanced hBounds
  have hDiameter : a + b ≤ M :=
    ordered_opposite_differences_le
      p q hP hQ hpM hqM i j a b hMax hMin
  omega

end SchurFormal
