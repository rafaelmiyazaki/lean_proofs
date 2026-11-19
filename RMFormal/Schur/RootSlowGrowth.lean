import RMFormal.Schur.BallMass

/-!
# The exact root factor in the slow-growth step

This module bridges the heavy seed inequality W/d < M(1)
to the geometric-growth hypothesis W <= alpha^ell * M(1)
with alpha = d^(1/ell). The algebra is an essential part of
the d>=2 branch of weighted Lemma 2.1.
-/

namespace SchurFormal

/-- Raising the ellth root d^(1/ell) to ell returns d. -/
theorem color_degree_root_pow
    (d ell : ℕ) (hd : 0 < d) (hell : 0 < ell) :
    ((d : ℝ) ^ (1 / (ell : ℝ))) ^ ell = (d : ℝ) := by
  simpa only [one_div] using
    (Real.rpow_inv_natCast_pow
      (x := (d : ℝ)) (n := ell)
      (by positivity : (0 : ℝ) ≤ d) (Nat.ne_of_gt hell))

/-- The root factor alpha is at least one for positive degree. -/
theorem color_degree_root_ge_one
    (d ell : ℕ) (hd : 1 ≤ d) (hell : 0 < ell) :
    (1 : ℝ) ≤ (d : ℝ) ^ (1 / (ell : ℝ)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hExp : (0 : ℝ) ≤ 1 / (ell : ℝ) := by positivity
  exact Real.one_le_rpow hdR hExp

/-- The strict heavy-seed inequality W/d < M1 implies the
    hypothesis of the slow-growth lemma with alpha=d^(1/ell). -/
theorem heavy_seed_to_growth
    (d ell : ℕ) (hd : 2 ≤ d) (hell : 0 < ell)
    (W M1 : ℝ) (hSeed : W / (d : ℝ) < M1) :
    W ≤ ((d : ℝ) ^ (1 / (ell : ℝ))) ^ ell * M1 := by
  rw [color_degree_root_pow d ell (by omega) hell]
  have hdPos : (0 : ℝ) < d := by
    exact_mod_cast (show 0 < d by omega)
  exact le_of_lt ((div_lt_iff₀ hdPos).mp hSeed)

/-- Root-factor slow-growth for an actual finite colored graph
provided its radius-one ball has more than W/d mass. -/
theorem exists_color_layer_from_heavy_seed
    {V C : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → C) (c : C) (v : V)
    (w : V → ℝ) (hw : ∀ x : V, 0 ≤ w x)
    (d ell : ℕ) (hd : 2 ≤ d) (hell : 0 < ell)
    (hSeed : (∑ x : V, w x) / (d : ℝ) <
      colorBallMass E c v w 1) :
    ∃ i ∈ Finset.Icc 1 ell,
      (∑ x ∈ (singleColorBall E c v (i + 1) \
        singleColorBall E c v i), w x) ≤
      ((d : ℝ) ^ (1 / (ell : ℝ)) - 1) *
        colorBallMass E c v w i := by
  exact exists_slow_color_layer E c v w hw ell hell
    ((d : ℝ) ^ (1 / (ell : ℝ)))
    (color_degree_root_ge_one d ell (by omega) hell)
    (heavy_seed_to_growth d ell hd hell
      (∑ x : V, w x) (colorBallMass E c v w 1) hSeed)

end SchurFormal
