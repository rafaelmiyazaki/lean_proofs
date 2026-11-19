import RMFormal.Schur.MinHeavySeed
import RMFormal.Schur.HeavyStarBall

/-!
# Choosing a heavy radius-one monochromatic ball

For any finite complete edge-colored graph with at least two vertices
and positive weights, select a minimum color-degree vertex v and
an incident color c with a heavy monochromatic star. If the minimum
color-degree d is at least two, the entire radius-one ball has
mass strictly greater than W/d.

This is the actual graph-theoretic seed construction needed before
the root-factor slow-growth lemma in Case d>=2 of Lemma 2.1.
-/

namespace SchurFormal

theorem exists_heavy_first_color_ball
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (w : V → ℝ)
    (hV : 2 ≤ (Finset.univ : Finset V).card)
    (hw : ∀ x : V, 0 < w x) :
    ∃ v : V, ∃ c ∈ incidentColors E Finset.univ v,
      0 < incidentColorDegree E Finset.univ v ∧
      (∀ x : V, incidentColorDegree E Finset.univ v ≤
        incidentColorDegree E Finset.univ x) ∧
      (2 ≤ incidentColorDegree E Finset.univ v →
        (∑ x : V, w x) / (incidentColorDegree E Finset.univ v : ℝ) <
          colorBallMass E c v w 1) := by
  classical
  obtain ⟨v, hv, c, hc, hdpos, hmin, hheavy⟩ :=
    exists_min_degree_heavy_color E Finset.univ w hV
      (by intro x _; exact hw x)
  refine ⟨v, c, hc, hdpos, ?_, ?_⟩
  · intro x
    exact hmin x (Finset.mem_univ _)
  · intro hd
    have hstar :
        (∑ x : V, w x) /
            (incidentColorDegree E Finset.univ v : ℝ) <
          w v + ∑ x ∈ Finset.univ.erase v,
            if c = E v x then w x else 0 :=
      heavy_neighbor_seed_mass
        (incidentColorDegree E Finset.univ v) hd
        (∑ x : V, w x) (w v)
        (∑ x ∈ Finset.univ.erase v,
          if c = E v x then w x else 0)
        (hw v) hheavy
    exact lt_of_lt_of_le hstar
      (heavy_star_mass_le_ball_one E c v w
        (fun x => (hw x).le))

end SchurFormal
