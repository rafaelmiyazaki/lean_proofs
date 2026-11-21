import RMFormal.Schur.Definitions

/-!
# Nonzero residue classes obstruct generalized Schur equations
Only the easy direction of the affine obstruction is attempted here.
All proofs are drafts pending a Lean compiler run.
-/

namespace SchurFormal

lemma list_sum_mod_of_constant_residue
    (xs : List ℕ) (d a : ℕ)
    (h : ∀ x ∈ xs, x % d = a % d) :
    xs.sum % d = (xs.length * a) % d := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x % d = a % d := h x (by simp)
    have htail : ∀ y ∈ xs, y % d = a % d := by
      intro y hy
      exact h y (by simp [hy])
    have hrest := ih htail
    simp only [List.sum_cons, List.length_cons]
    calc
      (x + xs.sum) % d = (x % d + xs.sum % d) % d := Nat.add_mod ..
      _ = (a % d + (xs.length * a) % d) % d := by rw [hx, hrest]
      _ = (a + xs.length * a) % d := (Nat.add_mod ..).symm
      _ = ((xs.length + 1) * a) % d := by congr 1; ring

/-- Any `(m+1,m)` equation inside a single residue class forces
    that class's residue to be zero. -/
theorem solution_forces_zero_residue
    {A : Set ℕ} {d a m : ℕ}
    (hA : ∀ x ∈ A, x % d = a % d)
    (hsol : HasEquation A (m + 1) m) :
    a % d = 0 := by
  rcases hsol with ⟨xs, ys, hxlen, hylen, hxs, hys, hsum⟩
  have hx := list_sum_mod_of_constant_residue xs d a
    (fun x hx => hA x (hxs x hx))
  have hy := list_sum_mod_of_constant_residue ys d a
    (fun y hy => hA y (hys y hy))
  have hcong : ((m + 1) * a) % d = (m * a) % d := by
    calc
      ((m + 1) * a) % d = xs.sum % d := by simpa [hxlen] using hx.symm
      _ = ys.sum % d := congrArg (fun n : ℕ => n % d) hsum
      _ = (m * a) % d := by simpa [hylen] using hy
  have hcancel : Nat.ModEq d (a + m * a) (0 + m * a) := by
    change (a + m * a) % d = (0 + m * a) % d
    simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hcong
  have hzero : Nat.ModEq d a 0 :=
    Nat.ModEq.add_right_cancel' (m * a) hcancel
  simpa [Nat.ModEq] using hzero

theorem nonzero_residue_avoids_all_lengths
    {A : Set ℕ} {d a : ℕ}
    (ha_pos : 0 < a) (ha_lt : a < d)
    (hA : ∀ x ∈ A, x % d = a) :
    ∀ m : ℕ, ¬ HasEquation A (m + 1) m := by
  intro m hsol
  have hrest : ∀ x ∈ A, x % d = a % d := by
    intro x hx
    rw [Nat.mod_eq_of_lt ha_lt]
    exact hA x hx
  have hzero : a % d = 0 := solution_forces_zero_residue hrest hsol
  rw [Nat.mod_eq_of_lt ha_lt] at hzero
  omega

end SchurFormal
