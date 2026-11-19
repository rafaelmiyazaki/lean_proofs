import RMFormal.Schur.RealWeights
import RMFormal.Schur.ColorDegrees

/-!
# Extracting the numerical bound of Lemma 2.1 from weighted mass ≤ 1

This is the final arithmetic step of the weighted local-coloring lemma:
if every vertex has at most q incident colors and total exact
vertex weight is at most one, then the number of vertices is at most
chi^q * (q!)^(1/ell).

The mass-at-most-one hypothesis is intentionally explicit.
Proving it for all q-local complete graphs is the remaining induction.
-/

namespace SchurFormal

/-- A lower bound on the per-vertex weight converts total mass ≤ 1
into the advertised numerical upper bound. -/
theorem count_bound_of_uniform_weight
    (chi ell q n : ℕ) (hchi : 0 < chi) (hell : 0 < ell)
    (hMass : (n : ℝ) * realColorWeight chi ell q ≤ 1) :
    (n : ℝ) ≤ (chi : ℝ) ^ q *
      (Nat.factorial q : ℝ) ^ (1 / (ell : ℝ)) := by
  have hchiR : 0 < (chi : ℝ) := by exact_mod_cast hchi
  have hFact : 0 < (Nat.factorial q : ℝ) := by positivity
  have hD : 0 < (chi : ℝ) ^ q *
      (Nat.factorial q : ℝ) ^ (1 / (ell : ℝ)) := by
    exact mul_pos (pow_pos hchiR _)
      (Real.rpow_pos_of_pos hFact _)
  have hDiv : (n : ℝ) /
      ((chi : ℝ) ^ q * (Nat.factorial q : ℝ) ^ (1 / (ell : ℝ))) ≤ 1 := by
    simpa [realColorWeight, div_eq_mul_inv] using hMass
  have hBound := (div_le_iff₀ hD).mp hDiv
  simpa using hBound

/-- Final numerical conclusion of Lemma 2.1, conditional only
on the total real vertex mass being ≤ 1. -/
theorem count_bound_of_total_vertex_mass
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (U : Finset V)
    (chi ell q : ℕ) (hchi : 0 < chi) (hell : 0 < ell)
    (hLocal : ∀ x ∈ U, incidentColorDegree E U x ≤ q)
    (hMass : (∑ x ∈ U,
        realColorWeight chi ell (incidentColorDegree E U x)) ≤ 1) :
    (U.card : ℝ) ≤ (chi : ℝ) ^ q *
      (Nat.factorial q : ℝ) ^ (1 / (ell : ℝ)) := by
  have hLower : (U.card : ℝ) * realColorWeight chi ell q ≤
      ∑ x ∈ U, realColorWeight chi ell (incidentColorDegree E U x) := by
    calc
      _ = ∑ x ∈ U, realColorWeight chi ell q := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ U,
          realColorWeight chi ell (incidentColorDegree E U x) := by
        apply Finset.sum_le_sum
        intro x hx
        exact real_color_weight_antitone chi ell
          (incidentColorDegree E U x) q
          (by omega) hell (hLocal x hx)
  exact count_bound_of_uniform_weight chi ell q U.card hchi hell
    (hLower.trans hMass)

end SchurFormal
