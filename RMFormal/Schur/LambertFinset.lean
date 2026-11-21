import RMFormal.Schur.WeightedZeroBlock

/-!
# Lambert's length estimate for primitive *indexed* zero-sum families

The summands are indexed by a finite set, so numerically equal terms
with distinct indices count with their full multiplicities. Primitivity
means that no nonempty proper subset of the index set sums to zero.

Combining the greedy reordering, the weighted zero-block lemma and
the interval counting result gives the bound |s| ≤ a+b.
-/

namespace SchurFormal

theorem lambert_length_of_primitive_finset
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℤ)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hzero : (∑ i ∈ s, f i) = 0)
    (hnz : ∀ i ∈ s, f i ≠ 0)
    (hbounds : ∀ i ∈ s, -(b : ℤ) ≤ f i ∧ f i ≤ (a : ℤ))
    (hprimitive : ∀ t : Finset α, t.Nonempty →
      t ⊆ s → t ≠ s → (∑ i ∈ t, f i) ≠ 0) :
    s.card ≤ a + b := by
  classical
  obtain ⟨order, hNodup, hOrder, hWalk⟩ :=
    exists_lambert_bounded_order s f a b 0
      (by simpa using hzero) hnz hbounds (by omega) (by omega)
  have hNoZero (ys : List α)
      (hsub : ys.Sublist order) (hne : ys ≠ [])
      (hlen : ys.length < order.length) :
      (ys.map f).sum ≠ 0 := by
    have hnys : ys.Nodup := hNodup.sublist hsub
    have hsubs : ys.toFinset ⊆ s := by
      intro x hx
      have hxList : x ∈ ys := List.mem_toFinset.mp hx
      have hxOrder : x ∈ order := hsub.subset hxList
      rw [← hOrder]
      exact List.mem_toFinset.mpr hxOrder
    have hproper : ys.toFinset ≠ s := by
      intro heq
      have hc := congrArg Finset.card heq
      rw [← hOrder] at hc
      have hysCard : ys.toFinset.card = ys.length :=
        List.toFinset_card_of_nodup hnys
      have horderCard : order.toFinset.card = order.length :=
        List.toFinset_card_of_nodup hNodup
      rw [hysCard, horderCard] at hc
      omega
    have hnonempty : ys.toFinset.Nonempty := by
      cases ys with
      | nil => exact False.elim (hne rfl)
      | cons x xs => exact ⟨x, by simp⟩
    have hsumFin :
        (∑ x ∈ ys.toFinset, f x) = (ys.map f).sum :=
      List.sum_toFinset f hnys
    intro hsum
    exact (hprimitive ys.toFinset hnonempty hsubs hproper)
      (by rw [hsumFin, hsum])
  have hInject :
      Function.Injective
        (fun j : Fin order.length =>
          (0 : ℤ) + ((order.take (j : ℕ)).map f).sum) := by
    simpa using weighted_proper_prefix_sums_injective order f hNoZero
  have hlen := lambert_length_of_distinct_prefixes
    f a b 0 order hWalk hInject
  rw [← hOrder]
  simpa [List.toFinset_card_of_nodup hNodup] using hlen

end SchurFormal
