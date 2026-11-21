import RMFormal.Schur.MinColorDegree
import RMFormal.Schur.HeavyNeighbor
import RMFormal.Schur.SeedMass

/-!
# Selecting a minimum-degree vertex and a heavy monochromatic star

The d ≥ 2 case of weighted Lemma 2.1 starts by selecting a
minimum incident-color-degree vertex v, and then a color c
that carries at least 1/d of the weight of all neighbors.
This module connects the independent verified lemmas and
obtains the closed-neighborhood seed mass > W/d.

The d = 1 case remains separate.
-/

namespace SchurFormal

/-- Select a minimum-degree vertex and its heavy incident color.
The selected closed color-neighborhood has mass exceeding one
d-th of the total vertex weight whenever d ≥ 2. -/
theorem exists_min_degree_heavy_color
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (U : Finset V)
    (w : V → ℝ)
    (hU : 2 ≤ U.card)
    (hW : ∀ x ∈ U, 0 < w x) :
    ∃ v ∈ U, ∃ c ∈ incidentColors E U v,
      (0 < incidentColorDegree E U v) ∧
      (∀ x ∈ U, incidentColorDegree E U v ≤
        incidentColorDegree E U x) ∧
      ((∑ x ∈ U, w x) - w v ≤
        (incidentColorDegree E U v : ℝ) *
          ∑ x ∈ U.erase v,
            if c = E v x then w x else 0) := by
  obtain ⟨v, hv, hdpos, hmin⟩ :=
    exists_min_incident_color_degree E U hU
  have hnonempty : (incidentColors E U v).Nonempty :=
    Finset.card_pos.mp hdpos
  obtain ⟨c, hc, hweight⟩ :=
    exists_heavy_incident_color E U v w hnonempty
  have hdecomp : (∑ x ∈ U.erase v, w x) + w v =
      ∑ x ∈ U, w x :=
    Finset.sum_erase_add U w hv
  refine ⟨v, hv, c, hc, hdpos, hmin, ?_⟩
  linarith

/-- The strong seed estimate used for slow-growth selection
in the minimum-degree d≥2 branch. -/
theorem exists_min_degree_heavy_closed_ball
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (U : Finset V)
    (w : V → ℝ)
    (hU : 2 ≤ U.card)
    (hW : ∀ x ∈ U, 0 < w x) :
    ∃ v ∈ U, ∃ c ∈ incidentColors E U v,
      (2 ≤ incidentColorDegree E U v) →
      (∑ x ∈ U, w x) / (incidentColorDegree E U v : ℝ) <
        w v + ∑ x ∈ U.erase v,
          if c = E v x then w x else 0 := by
  obtain ⟨v, hv, c, hc, _, _, hheavy⟩ :=
    exists_min_degree_heavy_color E U w hU hW
  refine ⟨v, hv, c, hc, ?_⟩
  intro hd
  exact heavy_neighbor_seed_mass (incidentColorDegree E U v) hd
    (∑ x ∈ U, w x) (w v)
    (∑ x ∈ U.erase v, if c = E v x then w x else 0)
    (hW v hv) hheavy

end SchurFormal
