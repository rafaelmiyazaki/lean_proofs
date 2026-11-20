import RMFormal.Schur.LambertGreedyStep

/-!
# Lambert's zero-sum theorem: a bounded greedy ordering

Given a finite family of nonzero integer summands totaling zero,
each in [-b,a], this module constructs an ordering of the summands
whose running partial sums stay in the interval (-b,a].

The proof works with a finite set of distinct indices, allowing
repeated numerical summands. The resulting walk is the constructive
core of Lambert's classical length estimate. A separate argument
showing that the partial sums are all distinct is still required.
-/

namespace SchurFormal

/-- An ordered walk whose running partial sums stay in (-b,a].
The sign selection recorded at each step follows Lambert's greedy
rule: choose a positive value when the current sum is nonpositive
and a negative value otherwise. -/
inductive LambertBoundedWalk {α : Type*}
    (f : α → ℤ) (a b : ℕ) : ℤ → List α → Prop where
  | nil (t : ℤ)
      (hlo : -(b : ℤ) < t)
      (hhi : t ≤ (a : ℤ)) :
      LambertBoundedWalk f a b t []
  | cons (t : ℤ) (i : α) (tail : List α)
      (hlo : -(b : ℤ) < t)
      (hhi : t ≤ (a : ℤ))
      (hsign : (t ≤ 0 ∧ 0 < f i) ∨ (0 < t ∧ f i < 0))
      (hrest : LambertBoundedWalk f a b (t + f i) tail) :
      LambertBoundedWalk f a b t (i :: tail)

/-- Reorder all unused nonzero terms so that every partial sum,
starting at t, stays in (-b,a]. This is independent of whether the
term values are pairwise distinct. -/
theorem exists_lambert_bounded_order
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℤ)
    (a b : ℕ) (t : ℤ)
    (hBalance : t + (∑ i ∈ s, f i) = 0)
    (hnz : ∀ i ∈ s, f i ≠ 0)
    (hbounds : ∀ i ∈ s, -(b : ℤ) ≤ f i ∧ f i ≤ (a : ℤ))
    (htlo : -(b : ℤ) < t) (hthi : t ≤ (a : ℤ)) :
    ∃ order : List α, order.Nodup ∧ order.toFinset = s ∧
      LambertBoundedWalk f a b t order := by
  classical
  have aux :
      ∀ n : ℕ, ∀ (s : Finset α), s.card = n →
      ∀ (t : ℤ),
      t + (∑ i ∈ s, f i) = 0 →
      (∀ i ∈ s, f i ≠ 0) →
      (∀ i ∈ s, -(b : ℤ) ≤ f i ∧ f i ≤ (a : ℤ)) →
      -(b : ℤ) < t → t ≤ (a : ℤ) →
      ∃ order : List α, order.Nodup ∧ order.toFinset = s ∧
        LambertBoundedWalk f a b t order := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hsCard t hBal hNZ hBounds htLow htHigh
      by_cases hEmpty : s = ∅
      · subst s
        refine ⟨[], by simp, by simp, ?_⟩
        exact LambertBoundedWalk.nil t htLow htHigh
      · have hsNonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
        obtain ⟨i, hi, hstepBounds, hsign⟩ :=
          exists_lambert_greedy_step s f a b t hsNonempty
            hBal hNZ hBounds htLow htHigh
        have hCardErase : (s.erase i).card < n := by
          have hcard := Finset.card_erase_of_mem hi
          omega
        have hEraseBalance :
            (t + f i) + (∑ j ∈ s.erase i, f j) = 0 := by
          have hdecomp :
              (∑ j ∈ s, f j) =
                (∑ j ∈ s.erase i, f j) + f i :=
            (s.sum_erase_add f hi).symm
          rw [hdecomp] at hBal
          omega
        have hNZErase : ∀ j ∈ s.erase i, f j ≠ 0 := by
          intro j hj
          exact hNZ j (Finset.mem_of_mem_erase hj)
        have hBoundsErase :
            ∀ j ∈ s.erase i, -(b : ℤ) ≤ f j ∧ f j ≤ (a : ℤ) := by
          intro j hj
          exact hBounds j (Finset.mem_of_mem_erase hj)
        obtain ⟨order, hNodup, hFinset, hWalk⟩ :=
          ih (s.erase i).card hCardErase (s.erase i) rfl
            (t + f i) hEraseBalance hNZErase hBoundsErase
            hstepBounds.1 hstepBounds.2
        refine ⟨i :: order, ?_, ?_, ?_⟩
        · apply List.nodup_cons.mpr
          constructor
          · intro hiOrder
            have hmem : i ∈ (order.toFinset) := by
              simpa using hiOrder
            rw [hFinset] at hmem
            simp at hmem
          · exact hNodup
        · simp [hFinset, Finset.insert_erase hi]
        · exact LambertBoundedWalk.cons t i order htLow htHigh hsign hWalk
  exact aux s.card s rfl t hBalance hnz hbounds htlo hthi

end SchurFormal
