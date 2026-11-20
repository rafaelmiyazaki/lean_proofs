import RMFormal.Schur.Corollary12

/-!
# Corollary 1.2 in the manuscript's original parameters

The already verified corollary uses a = d(m+1)+w and b = dm+w.
Here we show that, for every a > b > 0 with a ≤ 2b, the Euclidean
division of b by d = a-b supplies precisely those parameters.

This is an exact source-facing formulation of the corollary, expressed
in its equivalent integer-powered form.
-/

namespace SchurFormal

/-- Corollary 1.2 in terms of the original equation lengths a and b. -/
theorem corollary_1_2_source_parameters
    (a b r N : ℕ) (hba : b < a) (hab : a ≤ 2 * b)
    (hr : 0 < r) (color : ℕ → Fin r)
    (hAvoid : ∀ i : Fin r,
      ¬ HasEquation (ColorClass N color i) a b) :
    N ^ (b / (a - b)) ≤
      (2 * (b / (a - b)) + 1) ^ (r * (b / (a - b))) *
        Nat.factorial r := by
  let d : ℕ := a - b
  let m : ℕ := b / d
  let w : ℕ := b % d
  have hd : 0 < d := by
    dsimp [d]
    omega
  have hdb : d ≤ b := by
    dsimp [d]
    omega
  have hm : 0 < m := by
    change 0 < b / d
    exact Nat.div_pos hdb hd
  have hb : d * m + w = b := by
    dsimp [m, w]
    simpa only [Nat.add_comm] using (Nat.mod_add_div b d)
  have ha : d * (m + 1) + w = a := by
    have had : b + d = a := by
      dsimp [d]
      omega
    calc
      d * (m + 1) + w = (d * m + w) + d := by ring
      _ = b + d := by rw [hb]
      _ = a := had
  have hAvoid' : ∀ i : Fin r,
      ¬ HasEquation (ColorClass N color i)
        (d * (m + 1) + w) (d * m + w) := by
    intro i
    rw [ha, hb]
    exact hAvoid i
  exact corollary_1_2_unconditional m r N d w hm hr hd color hAvoid'

#print axioms corollary_1_2_source_parameters

end SchurFormal
