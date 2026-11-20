import RMFormal.Schur.Definitions

/-!
# Lemma 3.1: repetition and padding
This source has a successful Lean build and axiom audit.
-/

namespace SchurFormal

/-- Concatenate `t` copies of a list. -/
def repeatList (xs : List ℕ) : ℕ → List ℕ
  | 0 => []
  | t + 1 => xs ++ repeatList xs t

lemma repeatList_length (xs : List ℕ) (t : ℕ) :
    (repeatList xs t).length = t * xs.length := by
  induction t with
  | zero => simp [repeatList]
  | succ t ih =>
    simp only [repeatList, List.length_append, ih]
    simp [Nat.succ_mul, Nat.add_comm]

lemma repeatList_sum (xs : List ℕ) (t : ℕ) :
    (repeatList xs t).sum = t * xs.sum := by
  induction t with
  | zero => simp [repeatList]
  | succ t ih =>
    simp only [repeatList, List.sum_append, ih]
    simp [Nat.succ_mul, Nat.add_comm]

lemma repeatList_mem (xs : List ℕ) (t : ℕ) (z : ℕ)
    (hz : z ∈ repeatList xs t) : z ∈ xs := by
  induction t with
  | zero => simp [repeatList] at hz
  | succ t ih =>
    rcases List.mem_append.mp hz with h | h
    · exact h
    · exact ih h

/-- Paper's Lemma 3.1: repeat both sides and pad by a shared term.
    The assumption `u > 0` makes a padding term available. -/
theorem padding_lemma_3_1 {A : Set ℕ} {u v : ℕ}
    (hu : 0 < u) (h : HasEquation A u v)
    (t w : ℕ) :
    HasEquation A (u * t + w) (v * t + w) := by
  rcases h with ⟨xs, ys, hxlen, hylen, hxs, hys, hsum⟩
  obtain ⟨z, hz⟩ : ∃ z : ℕ, z ∈ A := by
    cases xs with
    | nil =>
      simp at hxlen
      omega
    | cons z tail =>
      exact ⟨z, hxs z (by simp)⟩
  refine ⟨repeatList xs t ++ List.replicate w z,
    repeatList ys t ++ List.replicate w z, ?_, ?_, ?_, ?_, ?_⟩
  · simp [repeatList_length, hxlen, Nat.mul_comm]
  · simp [repeatList_length, hylen, Nat.mul_comm]
  · intro s hs
    rcases List.mem_append.mp hs with hrepeat | hpad
    · exact hxs s (repeatList_mem xs t s hrepeat)
    · have heq : s = z := List.eq_of_mem_replicate hpad
      simpa [heq] using hz
  · intro s hs
    rcases List.mem_append.mp hs with hrepeat | hpad
    · exact hys s (repeatList_mem ys t s hrepeat)
    · have heq : s = z := List.eq_of_mem_replicate hpad
      simpa [heq] using hz
  · simp only [List.sum_append, repeatList_sum]
    rw [hsum]

end SchurFormal
