import RMFormal.Schur.Section5Diameter

/-!
# Section 5: sharpness of the length bound

The manuscript observes that the consecutive two-point set
{M-1,M}, with M≥2, first admits a Schur-type equation
at m=M-1. We independently verify the more general statement
that {u,u+1} has minimum possible solution length m=u.

This verifies the claimed sharpness example, but not the
universal upper bound m≤M-1.
-/

namespace SchurFormal

private theorem list_card_mul_le_sum
    (xs : List ℕ) (u : ℕ)
    (h : ∀ x ∈ xs, u ≤ x) :
    xs.length * u ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : u ≤ x := h x (by simp)
      have htail : ∀ y ∈ xs, u ≤ y := by
        intro y hy
        exact h y (by simp [hy])
      have hih := ih htail
      simp only [List.length_cons, List.sum_cons]
      rw [Nat.succ_mul]
      omega

private theorem list_sum_le_card_mul
    (xs : List ℕ) (u : ℕ)
    (h : ∀ x ∈ xs, x ≤ u) :
    xs.sum ≤ xs.length * u := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : x ≤ u := h x (by simp)
      have htail : ∀ y ∈ xs, y ≤ u := by
        intro y hy
        exact h y (by simp [hy])
      have hih := ih htail
      simp only [List.length_cons, List.sum_cons]
      rw [Nat.succ_mul]
      omega

/-- The pair of consecutive positive integers {u,u+1} admits
an (m+1,m) solution only for m≥u. -/
theorem consecutive_pair_length_lower_bound
    (u m : ℕ)
    (hsol : HasEquation ({u, u + 1} : Set ℕ) (m + 1) m) :
    u ≤ m := by
  rcases hsol with ⟨xs, ys, hxlen, hylen, hxs, hys, hsum⟩
  have hxmin : ∀ x ∈ xs, u ≤ x := by
    intro x hx
    have hmem := hxs x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h <;> omega
  have hymax : ∀ y ∈ ys, y ≤ u + 1 := by
    intro y hy
    have hmem := hys y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h <;> omega
  have hlo := list_card_mul_le_sum xs u hxmin
  have hhi := list_sum_le_card_mul ys (u + 1) hymax
  rw [hxlen] at hlo
  rw [hylen] at hhi
  have hleft : (m + 1) * u = m * u + u := by ring
  have hright : m * (u + 1) = m * u + m := by ring
  omega

/-- Conversely, for u>0 the equation with m=u is realized by
u+1 copies of u on the left and u copies of u+1 on the right. -/
theorem consecutive_pair_has_solution (u : ℕ) (hu : 0 < u) :
    HasEquation ({u, u + 1} : Set ℕ) (u + 1) u := by
  refine ⟨List.replicate (u + 1) u, List.replicate u (u + 1),
    by simp, by simp, ?_, ?_, ?_⟩
  · intro x hx
    have heq : x = u := List.eq_of_mem_replicate hx
    simp [heq]
  · intro y hy
    have heq : y = u + 1 := List.eq_of_mem_replicate hy
    simp [heq]
  · simp only [List.sum_replicate]
    ring

/-- The shortest positive m for the two-point extremal example is
exactly u. In particular, taking u=M-1 shows sharpness at M-1. -/
theorem consecutive_pair_exact_minimum (u : ℕ) (hu : 0 < u) :
    HasEquation ({u, u + 1} : Set ℕ) (u + 1) u ∧
    ∀ m : ℕ, 0 < m → m < u →
      ¬ HasEquation ({u, u + 1} : Set ℕ) (m + 1) m := by
  constructor
  · exact consecutive_pair_has_solution u hu
  · intro m _ hm hsol
    exact (Nat.not_le_of_gt hm) (consecutive_pair_length_lower_bound u m hsol)

end SchurFormal
