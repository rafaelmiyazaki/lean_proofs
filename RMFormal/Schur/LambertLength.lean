import RMFormal.Schur.LambertPrefix

/-!
# Lambert's bound from distinct bounded partial sums

This is the pigeonhole/counting half of the length bound.
A greedy walk of k terms in [-b,a] keeps all preceding partial
sums in (-b,a], an interval containing precisely a+b integers.

If those k partial sums are pairwise distinct, then k≤a+b.
The separate remaining obligation is to obtain their distinctness
from minimality of the original zero-sum family.
-/

namespace SchurFormal

/-- A bounded Lambert walk has length at most a+b provided the
partial sums immediately before its steps are pairwise distinct. -/
theorem lambert_length_of_distinct_prefixes
    {α : Type*} (f : α → ℤ) (a b : ℕ)
    (t : ℤ) (order : List α)
    (hwalk : LambertBoundedWalk f a b t order)
    (hDistinct : Function.Injective
      (fun j : Fin order.length =>
        t + ((order.take (j : ℕ)).map f).sum)) :
    order.length ≤ a + b := by
  let S : Fin order.length → ℤ :=
    fun j => t + ((order.take (j : ℕ)).map f).sum
  have hs (j : Fin order.length) :
      -(b : ℤ) < S j ∧ S j ≤ (a : ℤ) := by
    exact hwalk.prefix_bounds j.val j.isLt.le
  have hab : ((a + b : ℕ) : ℤ) = (a : ℤ) + (b : ℤ) := by
    push_cast
    ring
  let encode : Fin order.length → Fin (a + b) := fun j =>
    ⟨(S j + (b : ℤ) - 1).toNat, by
      have hj := hs j
      have hnonneg : 0 ≤ S j + (b : ℤ) - 1 := by omega
      have hupper : S j + (b : ℤ) - 1 < ((a + b : ℕ) : ℤ) := by
        omega
      omega⟩
  have hInjective : Function.Injective encode := by
    intro i j hij
    have hi := hs i
    have hj := hs j
    have hni : 0 ≤ S i + (b : ℤ) - 1 := by omega
    have hnj : 0 ≤ S j + (b : ℤ) - 1 := by omega
    have hti := Int.toNat_of_nonneg hni
    have htj := Int.toNat_of_nonneg hnj
    have hvals := congrArg Fin.val hij
    change (S i + (b : ℤ) - 1).toNat =
      (S j + (b : ℤ) - 1).toNat at hvals
    have hS : S i = S j := by omega
    exact hDistinct hS
  have hcard := Fintype.card_le_of_injective encode hInjective
  simpa using hcard

end SchurFormal
