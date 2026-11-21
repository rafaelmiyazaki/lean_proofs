import RMFormal.Schur.ResidueClass

/-!
# Optimality half of Theorem 1.3

Constructively color `[2^r-1]` with `r` colors: odds get a fresh
color and evens inherit the color of their halves. No color class
supports an equation with one more term on the left than on the right.
-/

namespace SchurFormal

/-- Recursively defined coloring with `k+1` colors. -/
def dyadicColor : (k : ℕ) → ℕ → Fin (k + 1)
  | 0, _ => 0
  | k + 1, n =>
    if n % 2 = 1 then 0 else (dyadicColor k (n / 2)).succ

private lemma dyadicColor_zero_odd (k n : ℕ)
    (h : dyadicColor (k + 1) n = 0) : n % 2 = 1 := by
  by_cases hodd : n % 2 = 1
  · exact hodd
  · simp [dyadicColor, hodd] at h

private lemma dyadicColor_succ_even (k n : ℕ) (j : Fin (k + 1))
    (h : dyadicColor (k + 1) n = j.succ) :
    n % 2 = 0 ∧ dyadicColor k (n / 2) = j := by
  have hnotodd : n % 2 ≠ 1 := by
    intro hodd
    simp [dyadicColor, hodd] at h
    have hv := congrArg Fin.val h
    simp at hv
  have heven : n % 2 = 0 := by omega
  have hs : (dyadicColor k (n / 2)).succ = j.succ := by
    simpa [dyadicColor, heven] using h
  exact ⟨heven, Fin.succ_inj.mp hs⟩

private lemma sum_ones (xs : List ℕ)
    (h : ∀ x ∈ xs, x = 1) : xs.sum = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x = 1 := h x (by simp)
    have htail : ∀ y ∈ xs, y = 1 := by
      intro y hy
      exact h y (by simp [hy])
    simpa [hx, ih htail, Nat.add_comm]

private lemma sum_half_of_even (xs : List ℕ)
    (h : ∀ x ∈ xs, x % 2 = 0) :
    2 * (xs.map (· / 2)).sum = xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x % 2 = 0 := h x (by simp)
    have htail : ∀ y ∈ xs, y % 2 = 0 := by
      intro y hy
      exact h y (by simp [hy])
    have hxdiv : 2 * (x / 2) = x := by omega
    simp only [List.map_cons, List.sum_cons]
    rw [mul_add, hxdiv, ih htail]

private lemma half_in_interval (k n : ℕ)
    (hn : n ∈ PositiveInterval (2 ^ (k + 1 + 1) - 1))
    (heven : n % 2 = 0) :
    n / 2 ∈ PositiveInterval (2 ^ (k + 1) - 1) := by
  dsimp [PositiveInterval] at hn ⊢
  have hp : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by
    simp [pow_succ, mul_comm]
  have hpositive : 0 < 2 ^ (k + 1) := by positivity
  omega

/-- Every color class of the dyadic coloring on `[2^(k+1)-1]`
avoids `(m+1,m)` equations for every nonnegative `m`. -/
theorem dyadicColor_avoids_all (k : ℕ) :
    ∀ i : Fin (k + 1), ∀ m : ℕ,
      ¬ HasEquation
        (ColorClass (2 ^ (k + 1) - 1) (dyadicColor k) i)
        (m + 1) m := by
  induction k with
  | zero =>
    intro i m hsol
    rcases hsol with ⟨xs, ys, hxlen, hylen, hxs, hys, hsum⟩
    have hxs1 : ∀ x ∈ xs, x = 1 := by
      intro x hx
      have hv := (hxs x hx).1
      change x ∈ PositiveInterval 1 at hv
      dsimp [PositiveInterval] at hv
      omega
    have hys1 : ∀ y ∈ ys, y = 1 := by
      intro y hy
      have hv := (hys y hy).1
      change y ∈ PositiveInterval 1 at hv
      dsimp [PositiveInterval] at hv
      omega
    have hxsum := sum_ones xs hxs1
    have hysum := sum_ones ys hys1
    omega
  | succ k ih =>
    intro i m hsol
    cases i using Fin.cases with
    | zero =>
      have hodd (x : ℕ)
          (hx : x ∈ ColorClass (2 ^ (k + 1 + 1) - 1)
             (dyadicColor (k + 1)) 0) : x % 2 = 1 :=
        dyadicColor_zero_odd k x hx.2
      have hnone := nonzero_residue_avoids_all_lengths
        (A := ColorClass (2 ^ (k + 1 + 1) - 1)
             (dyadicColor (k + 1)) 0)
        (d := 2) (a := 1) (by decide) (by decide) hodd
      exact hnone m hsol
    | succ j =>
      let A := ColorClass (2 ^ (k + 1 + 1) - 1)
        (dyadicColor (k + 1)) j.succ
      let B := ColorClass (2 ^ (k + 1) - 1) (dyadicColor k) j
      have pull (x : ℕ) (hx : x ∈ A) : x / 2 ∈ B := by
        have h_even := dyadicColor_succ_even k x j hx.2
        exact ⟨half_in_interval k x hx.1 h_even.1, h_even.2⟩
      have even (x : ℕ) (hx : x ∈ A) : x % 2 = 0 :=
        (dyadicColor_succ_even k x j hx.2).1
      rcases hsol with ⟨xs, ys, hxlen, hylen, hxs, hys, hsum⟩
      have hxs_even : ∀ x ∈ xs, x % 2 = 0 := by
        intro x hx
        exact even x (hxs x hx)
      have hys_even : ∀ y ∈ ys, y % 2 = 0 := by
        intro y hy
        exact even y (hys y hy)
      have hxsum := sum_half_of_even xs hxs_even
      have hysum := sum_half_of_even ys hys_even
      have hhalfsum : (xs.map (· / 2)).sum = (ys.map (· / 2)).sum := by
        omega
      have hlower : HasEquation B (m + 1) m := by
        refine ⟨xs.map (· / 2), ys.map (· / 2), ?_, ?_, ?_, ?_, ?_⟩
        · simpa using hxlen
        · simpa using hylen
        · intro z hz
          rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
          exact pull x (hxs x hx)
        · intro z hz
          rcases List.mem_map.mp hz with ⟨y, hy, rfl⟩
          exact pull y (hys y hy)
        · exact hhalfsum
      exact ih j m hlower

/-- Unconditional lower/optimality half of Theorem 1.3. -/
theorem two_power_lower : TwoPowerLower := by
  intro r hr
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  refine ⟨dyadicColor k, ?_⟩
  intro m _
  intro hmono
  rcases hmono with ⟨i, hsol⟩
  exact dyadicColor_avoids_all k i m hsol

end SchurFormal
