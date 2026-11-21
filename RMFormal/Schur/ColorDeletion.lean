import RMFormal.Schur.ColorDegrees

/-!
# Color disappearance under the deletion used in Lemma 2.1

Starting from an ambient vertex set U, a colored radius ball S,
its next layer T, and an independent color class S' inside S,
keep the vertices outside S ∪ T together with S'.

If every color-c neighbor in U of each x∈S' belongs to S∪T
and S' has no color-c edge, then every x∈S' loses color c
completely after the deletion. Consequently its incident
color-degree strictly decreases if c was originally incident.

This is the graph-theoretic deletion implication, conditional
only on the stated local-neighbor and independence hypotheses.
-/

namespace SchurFormal

def keptAfterLayerDeletion {V : Type*} [DecidableEq V]
    (U S T Sprime : Finset V) : Finset V :=
  (U \ (S ∪ T)) ∪ Sprime

theorem kept_vertices_subset {V : Type*} [DecidableEq V]
    {U S T Sprime : Finset V} (hSprime : Sprime ⊆ U) :
    keptAfterLayerDeletion U S T Sprime ⊆ U := by
  intro y hy
  change y ∈ (U \ (S ∪ T)) ∪ Sprime at hy
  rcases Finset.mem_union.mp hy with hOutside | hInside
  · exact (Finset.mem_sdiff.mp hOutside).1
  · exact hSprime hInside

/-- A vertex of S' has no surviving neighbor of the selected
color after deleting the layer and unselected vertices of S. -/
theorem selected_color_disappears
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (U S T Sprime : Finset V) (c : C)
    (hClosure : ∀ x ∈ Sprime, ∀ y ∈ U, E x y = c → y ∈ S ∪ T)
    (hIndependent : ∀ x ∈ Sprime, ∀ y ∈ Sprime,
      x ≠ y → E x y ≠ c)
    (x : V) (hx : x ∈ Sprime) :
    c ∉ incidentColors E (keptAfterLayerDeletion U S T Sprime) x := by
  apply incident_color_absent E (keptAfterLayerDeletion U S T Sprime) x c
  intro y hy hyne heq
  change y ∈ (U \ (S ∪ T)) ∪ Sprime at hy
  rcases Finset.mem_union.mp hy with hOutside | hInside
  · have hInU := (Finset.mem_sdiff.mp hOutside).1
    have hNot := (Finset.mem_sdiff.mp hOutside).2
    exact hNot (hClosure x hx y hInU heq)
  · exact hIndependent x hx y hInside hyne.symm heq

/-- The weight-relevant conclusion: every selected vertex loses
at least one incident color. -/
theorem selected_color_degree_strictly_drops
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (U S T Sprime : Finset V) (c : C)
    (hSprime : Sprime ⊆ U)
    (hClosure : ∀ x ∈ Sprime, ∀ y ∈ U, E x y = c → y ∈ S ∪ T)
    (hIndependent : ∀ x ∈ Sprime, ∀ y ∈ Sprime,
      x ≠ y → E x y ≠ c)
    (x : V) (hx : x ∈ Sprime)
    (hIncident : c ∈ incidentColors E U x) :
    incidentColorDegree E (keptAfterLayerDeletion U S T Sprime) x <
      incidentColorDegree E U x := by
  exact incident_color_degree_strict_drop E
    (kept_vertices_subset hSprime) x c hIncident
    (selected_color_disappears E U S T Sprime c
      hClosure hIndependent x hx)

end SchurFormal
