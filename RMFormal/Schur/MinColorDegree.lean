import RMFormal.Schur.ColorDegrees

/-!
# Minimum incident-color degree in a finite colored complete graph

On any finite vertex set with at least two vertices, choose a
vertex of minimum incident color-degree. Its color-degree is positive:
an edge to another vertex carries at least one color.

This is the first combinatorial choice in the weighted induction
of Lemma 2.1.
-/

namespace SchurFormal

/-- At least two vertices force another vertex distinct from v. -/
private theorem exists_other_vertex
    {V : Type*} [DecidableEq V]
    (U : Finset V) (hU : 2 ≤ U.card) (v : V) (hv : v ∈ U) :
    ∃ y ∈ U, y ≠ v := by
  by_contra hnone
  have hAll (y : V) (hy : y ∈ U) : y = v := by
    by_contra hneq
    exact hnone ⟨y, hy, hneq⟩
  have hSmall : U.card ≤ 1 := Finset.card_le_one_iff.mpr (by
    intro a b ha hb
    exact (hAll a ha).trans (hAll b hb).symm)
  omega

/-- Finite complete graphs with at least two vertices have a
minimum-color-degree vertex of positive color-degree. -/
theorem exists_min_incident_color_degree
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (U : Finset V)
    (hU : 2 ≤ U.card) :
    ∃ v ∈ U,
      0 < incidentColorDegree E U v ∧
      ∀ x ∈ U, incidentColorDegree E U v ≤
        incidentColorDegree E U x := by
  have hNonempty : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv, hMin⟩ :=
    Finset.exists_min_image U (incidentColorDegree E U) hNonempty
  obtain ⟨y, hy, hyne⟩ := exists_other_vertex U hU v hv
  have hColor : E v y ∈ incidentColors E U v :=
    Finset.mem_image.mpr
      ⟨y, Finset.mem_erase.mpr ⟨hyne, hy⟩, rfl⟩
  have hpos : 0 < incidentColorDegree E U v :=
    Finset.card_pos.mpr ⟨E v y, hColor⟩
  exact ⟨v, hv, hpos, hMin⟩

end SchurFormal
