import RMFormal.Schur.WeightedLemma21
import RMFormal.Schur.FiniteDifferenceWalk

/-!
# Applying the weighted local-coloring lemma to Schur equations

The edge-colored complete graph on Fin N gets edge color
color(|x-y|). If no color class has an (m+1,m) solution,
then each monochromatic radius-m ball is properly (2m+1)-colorable
by signed-charge coloring. Its incident color-degree is at most r.

The weighted lemma then yields the exact REAL numerical bound
N <= (2m+1)^r * (r!)^(1/m).

The final conversion to the natural-number power formulation of
Theorem 1.1 is carried out separately.
-/

namespace SchurFormal

theorem finite_schur_bound_real
    (m r N : ℕ) (hm : 0 < m) (hr : 0 < r)
    (color : ℕ → Fin r)
    (hAvoid : ∀ i : Fin r,
      ¬ HasEquation (ColorClass N color i) (m + 1) m) :
    (N : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) ^ r *
      (Nat.factorial r : ℝ) ^ (1 / (m : ℝ)) := by
  classical
  let E : Fin N → Fin N → Fin r :=
    finiteDifferenceColor color
  have hSym : ∀ x y : Fin N, E x y = E y x := by
    intro x y
    exact finite_difference_color_symmetric color x y
  have hDegree (v : Fin N) :
      incidentColorDegree E Finset.univ v ≤ r := by
    unfold incidentColorDegree
    have hSub :
        incidentColors E Finset.univ v ⊆ (Finset.univ : Finset (Fin r)) :=
      Finset.subset_univ _
    have hc := Finset.card_le_card hSub
    simpa using hc
  have hLocal (v : Fin N) (c : Fin r) :
      ∃ col : Fin N → Fin (2 * m + 1),
        ∀ x ∈ singleColorBall E c v m,
        ∀ y ∈ singleColorBall E c v m,
          x ≠ y → E x y = c → col x ≠ col y :=
    finite_ball_charge_coloring color c v m (hAvoid c)
  have hBound :=
    weighted_local_coloring_lemma E hSym
      (2 * m + 1) m r (by omega) hm hDegree hLocal
  simpa [E] using hBound

end SchurFormal
