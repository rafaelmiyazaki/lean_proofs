import RMFormal.Schur.MassAccounting
import RMFormal.Schur.WeightGain
import RMFormal.Schur.ColorDeletion

/-!
# Actual real-weight comparison after deletion of a color layer

This specializes the abstract mass-accounting theorem to the *exact*
vertex weights of Lemma 2.1 and graph-theoretic incident color degrees.

If selected vertices lose at least one color, their original degrees
are at least d, and the slow layer factor alpha does not exceed
d^(1/ell), then the total weight does not decrease.

The remaining induction requires constructing the slow layer and
independent heavy class with the stated hypotheses.
-/

namespace SchurFormal

/-- The real weight of x in the colored graph induced on U. -/
noncomputable def graphVertexWeight
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (chi ell : ℕ) (U : Finset V) (x : V) : ℝ :=
  realColorWeight chi ell (incidentColorDegree E U x)

/-- The exact vertex-weight comparison underlying the inductive
deletion step of weighted local-coloring Lemma 2.1. -/
theorem weighted_graph_deletion_preserves_mass
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (chi ell dmin : ℕ)
    (hchi : 0 < chi) (hell : 0 < ell)
    (U S T P : Finset V) (hS : S ⊆ U) (hT : T ⊆ U)
    (hST : Disjoint S T) (hP : P ⊆ S)
    (alpha : ℝ) (hAlpha : 1 ≤ alpha)
    (hAlphaMax : alpha ≤ (dmin : ℝ) ^ (1 / (ell : ℝ)))
    (hSelectedDegree : ∀ x ∈ P,
      incidentColorDegree E (keptAfterLayerDeletion U S T P) x <
        incidentColorDegree E U x)
    (hMinDegree : ∀ x ∈ P, dmin ≤ incidentColorDegree E U x)
    (hSlow : (∑ x ∈ T, graphVertexWeight E chi ell U x) ≤
      (alpha - 1) * (∑ x ∈ S, graphVertexWeight E chi ell U x))
    (hHeavy : (∑ x ∈ S, graphVertexWeight E chi ell U x) ≤
      (chi : ℝ) * (∑ x ∈ P, graphVertexWeight E chi ell U x)) :
    (∑ x ∈ U, graphVertexWeight E chi ell U x) ≤
      ∑ x ∈ keptAfterLayerDeletion U S T P,
        graphVertexWeight E chi ell (keptAfterLayerDeletion U S T P) x := by
  let K := keptAfterLayerDeletion U S T P
  have hPsub : P ⊆ U := hP.trans hS
  have hKsub : K ⊆ U := kept_vertices_subset hPsub
  have hOutside : ∀ x ∈ U \ (S ∪ T),
      graphVertexWeight E chi ell U x ≤ graphVertexWeight E chi ell K x := by
    intro x _
    dsimp [graphVertexWeight]
    exact real_color_weight_antitone chi ell
      (incidentColorDegree E K x) (incidentColorDegree E U x)
      (by omega) hell (incident_color_degree_mono E hKsub x)
  have hSelected : ∀ x ∈ P,
      ((chi : ℝ) * alpha) * graphVertexWeight E chi ell U x ≤
        graphVertexWeight E chi ell K x := by
    intro x hx
    have hGain := real_color_weight_strict_gain chi ell
      (incidentColorDegree E U x) (incidentColorDegree E K x) dmin
      hchi hell (hSelectedDegree x hx) (hMinDegree x hx)
    have hW : 0 ≤ graphVertexWeight E chi ell U x :=
      (real_color_weight_pos chi ell (incidentColorDegree E U x) hchi hell).le
    have hChi : 0 ≤ (chi : ℝ) := by positivity
    have hBefore :
        ((chi : ℝ) * alpha) * graphVertexWeight E chi ell U x ≤
          ((chi : ℝ) * (dmin : ℝ) ^ (1 / (ell : ℝ))) *
            graphVertexWeight E chi ell U x :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hAlphaMax hChi) hW
    exact hBefore.trans (by simpa only [graphVertexWeight] using hGain)
  exact total_mass_preserved_by_layer_deletion
    U S T P hS hT hST hP
    (graphVertexWeight E chi ell U)
    (graphVertexWeight E chi ell K)
    (chi : ℝ) alpha hAlpha hOutside hSelected hSlow hHeavy

end SchurFormal
