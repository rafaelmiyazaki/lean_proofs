import RMFormal.Schur.UniversalWeightedInduction

/-!
# The weighted local-coloring lemma in the paper's exact form

Lemma 2.1 assumes proper chi-colorability of the color-c
subgraph induced by the *radius-ell* ball. By nesting of
monochromatic balls this implies the all-radii version used
during the weighted induction.

Combining that observation with the verified induction gives
  n <= chi^q * (q!)^(1/ell).
-/

namespace SchurFormal

theorem colorability_all_smaller_balls
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (chi ell : ℕ)
    (hAtEll : ∀ (v : V) (c : C),
      ∃ color : V → Fin chi,
        ∀ x ∈ singleColorBall E c v ell,
        ∀ y ∈ singleColorBall E c v ell,
          x ≠ y → E x y = c → color x ≠ color y) :
    ∀ (v : V) (c : C) (i : ℕ),
      1 ≤ i → i ≤ ell →
      ∃ color : V → Fin chi,
        ∀ x ∈ singleColorBall E c v i,
        ∀ y ∈ singleColorBall E c v i,
          x ≠ y → E x y = c → color x ≠ color y := by
  intro v c i _ hiEll
  obtain ⟨color, hProper⟩ := hAtEll v c
  refine ⟨color, ?_⟩
  intro x hx y hy hne hedge
  exact hProper x (single_color_ball_mono E c v hiEll hx)
    y (single_color_ball_mono E c v hiEll hy) hne hedge

/-- Weighted local-coloring Lemma 2.1, exact bound. -/
theorem weighted_local_coloring_lemma
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C)
    (hSym : ∀ x y : V, E x y = E y x)
    (chi ell q : ℕ) (hchi : 2 ≤ chi) (hell : 0 < ell)
    (hLocalDegree : ∀ v : V,
      incidentColorDegree E Finset.univ v ≤ q)
    (hLocalBall : ∀ (v : V) (c : C),
      ∃ color : V → Fin chi,
        ∀ x ∈ singleColorBall E c v ell,
        ∀ y ∈ singleColorBall E c v ell,
          x ≠ y → E x y = c → color x ≠ color y) :
    (Fintype.card V : ℝ) ≤ (chi : ℝ) ^ q *
      (Nat.factorial q : ℝ) ^ (1 / (ell : ℝ)) := by
  have hDegrees : ∀ x ∈ (Finset.univ : Finset V),
      incidentColorDegree E Finset.univ x ≤ q := by
    intro x _
    exact hLocalDegree x
  have hAll :=
    colorability_all_smaller_balls E chi ell hLocalBall
  have h :=
    weighted_local_bound_from_local_colorings E hSym
      Finset.univ chi ell q (by omega) hell hDegrees hAll
  simpa using h

end SchurFormal
