import RMFormal.Schur.GraphLayers
import RMFormal.Schur.SlowGrowth

/-!
# Masses of monochromatic graph balls

The large-minimum-color-degree case of the weighted lemma uses
cumulative weights of color-c radius balls. This module connects
the abstract slow-growth lemma to the actual finite graph sets.
-/

namespace SchurFormal

/-- Cumulative real mass in the monochromatic radius-i ball. -/
noncomputable def colorBallMass
    {V C : Type*} [Fintype V]
    (E : V → V → C) (c : C) (a : V)
    (w : V → ℝ) (i : ℕ) : ℝ :=
  ∑ x ∈ singleColorBall E c a i, w x

theorem single_color_ball_mono
    {V C : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → C) (c : C) (a : V)
    {i j : ℕ} (hij : i ≤ j) :
    singleColorBall E c a i ⊆ singleColorBall E c a j := by
  classical
  intro x hx
  have hrad : WithinSingleColorRadius E c a i x := by
    unfold singleColorBall at hx
    exact (Finset.mem_filter.mp hx).2
  rcases hrad with ⟨n, hn, hp⟩
  unfold singleColorBall
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨n, by omega, hp⟩⟩

theorem ball_mass_le_total
    {V C : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → C) (c : C) (a : V)
    (w : V → ℝ) (hw : ∀ x : V, 0 ≤ w x)
    (i : ℕ) :
    colorBallMass E c a w i ≤ ∑ x : V, w x := by
  classical
  unfold colorBallMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ _) (by intro x _ _; exact hw x)

theorem ball_mass_succ_eq_add_layer
    {V C : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → C) (c : C) (a : V)
    (w : V → ℝ) (i : ℕ) :
    colorBallMass E c a w (i + 1) =
      colorBallMass E c a w i +
        ∑ x ∈ (singleColorBall E c a (i + 1) \
          singleColorBall E c a i), w x := by
  classical
  have hsub := single_color_ball_mono E c a (Nat.le_succ i)
  have hsum := Finset.sum_sdiff hsub (f := w)
  unfold colorBallMass
  linarith

/-- The exact graph-ball version of the slow-layer argument.
The only remaining numerical requirement is an initial ball
mass at least T/alpha^ell. -/
theorem exists_slow_color_layer
    {V C : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → C) (c : C) (a : V)
    (w : V → ℝ) (hw : ∀ x : V, 0 ≤ w x)
    (ell : ℕ) (hEll : 0 < ell) (alpha : ℝ) (hAlpha : 1 ≤ alpha)
    (hSeed : (∑ x : V, w x) ≤
      alpha ^ ell * colorBallMass E c a w 1) :
    ∃ i ∈ Finset.Icc 1 ell,
      (∑ x ∈ singleColorBall E c a (i + 1) \
        singleColorBall E c a i, w x) ≤
      (alpha - 1) * colorBallMass E c a w i := by
  have htotal : colorBallMass E c a w (ell + 1) ≤
      ∑ x : V, w x := ball_mass_le_total E c a w hw (ell + 1)
  obtain ⟨i, hi, hslow⟩ :=
    exists_small_new_layer ell hEll alpha
      (∑ x : V, w x) hAlpha
      (colorBallMass E c a w) htotal hSeed
  refine ⟨i, hi, ?_⟩
  rw [ball_mass_succ_eq_add_layer] at hslow
  linarith

end SchurFormal
