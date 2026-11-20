import RMFormal.Schur.Section5Diameter

/-!
# Lambert's minimal zero-sum bound: the greedy step

For a finite set of remaining nonzero integer summands whose total
is the negative of the current partial sum, choose a positive term
when the partial sum is nonpositive, and a negative term otherwise.

If all summands lie in [-b,a] and the current partial sum lies in
(-b,a], the next partial sum remains in (-b,a]. This is a constructive
local ingredient of Lambert's minimal zero-sum argument. It does not
by itself establish the global length bound.
-/

namespace SchurFormal

private theorem exists_positive_of_nonnegative_sum
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℤ)
    (hs : s.Nonempty)
    (hnz : ∀ i ∈ s, f i ≠ 0)
    (hsum : 0 ≤ ∑ i ∈ s, f i) :
    ∃ i ∈ s, 0 < f i := by
  classical
  by_contra h
  have hneg (i : α) (hi : i ∈ s) : f i ≤ -1 := by
    have hno : ¬ 0 < f i := by
      intro hp
      exact h ⟨i, hi, hp⟩
    have hneq := hnz i hi
    omega
  have hsum_le :
      (∑ i ∈ s, f i) ≤ (∑ _i ∈ s, (-1 : ℤ)) :=
    Finset.sum_le_sum hneg
  have hconst : (∑ _i ∈ s, (-1 : ℤ)) = -(s.card : ℤ) := by
    simp
  have hcard : 0 < s.card := Finset.card_pos.mpr hs
  omega

private theorem exists_negative_of_nonpositive_sum
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℤ)
    (hs : s.Nonempty)
    (hnz : ∀ i ∈ s, f i ≠ 0)
    (hsum : (∑ i ∈ s, f i) ≤ 0) :
    ∃ i ∈ s, f i < 0 := by
  classical
  by_contra h
  have hpos (i : α) (hi : i ∈ s) : (1 : ℤ) ≤ f i := by
    have hno : ¬ f i < 0 := by
      intro hp
      exact h ⟨i, hi, hp⟩
    have hneq := hnz i hi
    omega
  have hsum_ge :
      (∑ _i ∈ s, (1 : ℤ)) ≤ (∑ i ∈ s, f i) :=
    Finset.sum_le_sum hpos
  have hconst : (∑ _i ∈ s, (1 : ℤ)) = (s.card : ℤ) := by
    simp
  have hcard : 0 < s.card := Finset.card_pos.mpr hs
  omega

/-- In the greedy proof of Lambert's theorem one can always select
a remaining summand of the appropriate sign, while preserving the
interval bound for the next partial sum. -/
theorem exists_lambert_greedy_step
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℤ)
    (a b : ℕ) (t : ℤ)
    (hs : s.Nonempty)
    (hBalance : t + (∑ i ∈ s, f i) = 0)
    (hnz : ∀ i ∈ s, f i ≠ 0)
    (hbounds : ∀ i ∈ s, -(b : ℤ) ≤ f i ∧ f i ≤ (a : ℤ))
    (htlo : -(b : ℤ) < t) (hthi : t ≤ (a : ℤ)) :
    ∃ i ∈ s,
      (-(b : ℤ) < t + f i ∧ t + f i ≤ (a : ℤ)) ∧
      ((t ≤ 0 ∧ 0 < f i) ∨ (0 < t ∧ f i < 0)) := by
  by_cases ht : t ≤ 0
  · have hsum : 0 ≤ ∑ i ∈ s, f i := by omega
    obtain ⟨i, hi, hpos⟩ :=
      exists_positive_of_nonnegative_sum s f hs hnz hsum
    obtain ⟨hlo, hhi⟩ := hbounds i hi
    refine ⟨i, hi, ?_, Or.inl ⟨ht, hpos⟩⟩
    constructor <;> omega
  · have htpos : 0 < t := by omega
    have hsum : (∑ i ∈ s, f i) ≤ 0 := by omega
    obtain ⟨i, hi, hneg⟩ :=
      exists_negative_of_nonpositive_sum s f hs hnz hsum
    obtain ⟨hlo, hhi⟩ := hbounds i hi
    refine ⟨i, hi, ?_, Or.inr ⟨htpos, hneg⟩⟩
    constructor <;> omega

end SchurFormal
