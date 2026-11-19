import RMFormal.Schur.ColorDeletion
import RMFormal.Schur.WeightedDeletion

/-!
# Exact mass accounting for weighted-lemma vertex deletion

Given a finite ambient vertex set U and disjoint S,T⊆U,
replace S∪T by a selected class P⊆S. If individual weights
outside S∪T do not decrease, while selected weights increase
by a factor gain, the new total mass has an explicit lower
bound. The slow-growth inequality and heavy-class inequality
then ensure mass preservation.

This is a nontrivial combinatorial aggregation step in
Lemma 2.1, but NOT the full weighted graph induction.
-/

namespace SchurFormal

/-- Exact partition of old mass into surviving outside vertices,
the radius ball S, and the next layer T. -/
theorem old_mass_partition
    {V : Type*} [DecidableEq V]
    (U S T : Finset V) (hS : S ⊆ U) (hT : T ⊆ U)
    (hST : Disjoint S T) (w : V → ℝ) :
    (∑ v ∈ U \ (S ∪ T), w v) +
      (∑ v ∈ S, w v) + (∑ v ∈ T, w v) =
      ∑ v ∈ U, w v := by
  have hUnion : S ∪ T ⊆ U := Finset.union_subset hS hT
  have hPart :
      (∑ v ∈ U \ (S ∪ T), w v) +
        (∑ v ∈ S ∪ T, w v) = ∑ v ∈ U, w v := by
    rw [Finset.sum_sdiff hUnion]
    ring
  rw [Finset.sum_union hST] at hPart
  linarith

/-- Under pointwise lower bounds, the mass after deleting
T and S\P has the sharp needed lower bound. -/
theorem mass_after_deletion_lower_bound
    {V : Type*} [DecidableEq V]
    (U S T P : Finset V)
    (hS : S ⊆ U) (hT : T ⊆ U)
    (hST : Disjoint S T) (hP : P ⊆ S)
    (wOld wNew : V → ℝ) (gain : ℝ)
    (hOutside : ∀ x ∈ U \ (S ∪ T), wOld x ≤ wNew x)
    (hSelected : ∀ x ∈ P, gain * wOld x ≤ wNew x) :
    (∑ x ∈ U, wOld x) - (∑ x ∈ S, wOld x) -
      (∑ x ∈ T, wOld x) + gain * (∑ x ∈ P, wOld x) ≤
      ∑ x ∈ keptAfterLayerDeletion U S T P, wNew x := by
  let D := U \ (S ∪ T)
  have hD : Disjoint D P := by
    apply Finset.disjoint_left.mpr
    intro x hx hp
    exact (Finset.mem_sdiff.mp hx).2
      (Finset.mem_union.mpr (Or.inl (hP hp)))
  have hOutsideSum : (∑ x ∈ D, wOld x) ≤
      ∑ x ∈ D, wNew x := by
    apply Finset.sum_le_sum
    intro x hx
    exact hOutside x hx
  have hSelectedSum : gain * (∑ x ∈ P, wOld x) ≤
      ∑ x ∈ P, wNew x := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    exact hSelected x hx
  have hOld := old_mass_partition U S T hS hT hST wOld
  have hNew : (∑ x ∈ keptAfterLayerDeletion U S T P, wNew x) =
      (∑ x ∈ D, wNew x) + (∑ x ∈ P, wNew x) := by
    change (∑ x ∈ D ∪ P, wNew x) = _
    exact Finset.sum_union hD
  rw [hNew]
  linarith

/-- Integrated abstract mass-preservation step: if P carries at
least 1/chi of S and the next layer is slow-growing, deleting
S\P and T does not decrease the total mass provided each selected
vertex's weight grows by chi*alpha. -/
theorem total_mass_preserved_by_layer_deletion
    {V : Type*} [DecidableEq V]
    (U S T P : Finset V)
    (hS : S ⊆ U) (hT : T ⊆ U)
    (hST : Disjoint S T) (hP : P ⊆ S)
    (wOld wNew : V → ℝ) (chi alpha : ℝ)
    (hAlpha : 1 ≤ alpha)
    (hOutside : ∀ x ∈ U \ (S ∪ T), wOld x ≤ wNew x)
    (hSelected : ∀ x ∈ P,
      (chi * alpha) * wOld x ≤ wNew x)
    (hLayer : (∑ x ∈ T, wOld x) ≤
      (alpha - 1) * (∑ x ∈ S, wOld x))
    (hHeavy : (∑ x ∈ S, wOld x) ≤
      chi * (∑ x ∈ P, wOld x)) :
    (∑ x ∈ U, wOld x) ≤
      ∑ x ∈ keptAfterLayerDeletion U S T P, wNew x := by
  have hLower := mass_after_deletion_lower_bound
    U S T P hS hT hST hP wOld wNew
    (chi * alpha) hOutside hSelected
  exact weighted_deletion_preserves_mass
    (∑ x ∈ U, wOld x)
    (∑ x ∈ keptAfterLayerDeletion U S T P, wNew x)
    (∑ x ∈ S, wOld x)
    (∑ x ∈ T, wOld x)
    (∑ x ∈ P, wOld x)
    chi alpha hAlpha hLayer hHeavy hLower

end SchurFormal
