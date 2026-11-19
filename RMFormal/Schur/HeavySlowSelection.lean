import RMFormal.Schur.HeavySeedBall
import RMFormal.Schur.RootSlowGrowth

/-!
# Heavy seed and slow layer chosen from a minimum color-degree vertex

This composes the exact graph-theoretic heavy-color choice with
the geometric root-factor slow-growth lemma. It produces the
radius i needed in the d>=2 branch of Lemma 2.1.
-/

namespace SchurFormal

theorem exists_heavy_slow_color_layer
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (w : V → ℝ)
    (hV : 2 ≤ (Finset.univ : Finset V).card)
    (hw : ∀ x : V, 0 < w x)
    (ell : ℕ) (hell : 0 < ell) :
    ∃ v : V, ∃ c ∈ incidentColors E Finset.univ v,
      0 < incidentColorDegree E Finset.univ v ∧
      (∀ x : V, incidentColorDegree E Finset.univ v ≤
        incidentColorDegree E Finset.univ x) ∧
      (2 ≤ incidentColorDegree E Finset.univ v →
        ∃ i ∈ Finset.Icc 1 ell,
          (∑ x ∈ (singleColorBall E c v (i + 1) \
            singleColorBall E c v i), w x) ≤
          ((incidentColorDegree E Finset.univ v : ℝ) ^
             (1 / (ell : ℝ)) - 1) *
            colorBallMass E c v w i) := by
  obtain ⟨v, c, hc, hdpos, hmin, hseed⟩ :=
    exists_heavy_first_color_ball E w hV hw
  refine ⟨v, c, hc, hdpos, hmin, ?_⟩
  intro hd
  exact exists_color_layer_from_heavy_seed E c v w
    (fun x => (hw x).le)
    (incidentColorDegree E Finset.univ v) ell hd hell (hseed hd)

end SchurFormal
