import Mathlib

/-!
# Incident-color degrees under vertex deletion

This is the graph-theoretic bookkeeping for Lemma 2.1.
Restricting a colored complete graph to fewer vertices cannot
increase the number of distinct colors incident at a vertex.
If a specific incident color disappears, the number of
incident colors strictly decreases.

The edge-coloring is an arbitrary function E : V → V → C;
the proofs do not need the symmetry condition, hence apply
to every undirected edge-coloring as a special case.
-/

namespace SchurFormal

/-- Colors on edges from x to other vertices of S. -/
def incidentColors {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (S : Finset V) (x : V) : Finset C :=
  (S.erase x).image (E x)

/-- The color-degree of x in the induced colored graph on S. -/
def incidentColorDegree {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (S : Finset V) (x : V) : ℕ :=
  (incidentColors E S x).card

theorem incident_colors_mono {V C : Type*}
    [DecidableEq V] [DecidableEq C]
    (E : V → V → C) {S T : Finset V}
    (hST : S ⊆ T) (x : V) :
    incidentColors E S x ⊆ incidentColors E T x := by
  intro c hc
  rcases Finset.mem_image.mp hc with ⟨y, hy, rfl⟩
  have hne := (Finset.mem_erase.mp hy).1
  have hmem := (Finset.mem_erase.mp hy).2
  apply Finset.mem_image.mpr
  exact ⟨y, Finset.mem_erase.mpr ⟨hne, hST hmem⟩, rfl⟩

/-- Deleting vertices never increases color-degree. -/
theorem incident_color_degree_mono {V C : Type*}
    [DecidableEq V] [DecidableEq C]
    (E : V → V → C) {S T : Finset V}
    (hST : S ⊆ T) (x : V) :
    incidentColorDegree E S x ≤ incidentColorDegree E T x :=
  Finset.card_le_card (incident_colors_mono E hST x)

/-- If all surviving edges at x have colors distinct from c,
then x loses color c completely. -/
theorem incident_color_absent
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (S : Finset V) (x : V) (c : C)
    (h : ∀ y ∈ S, y ≠ x → E x y ≠ c) :
    c ∉ incidentColors E S x := by
  intro hc
  obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hc
  have hne := (Finset.mem_erase.mp hy).1
  have hmem := (Finset.mem_erase.mp hy).2
  exact h y hmem hne heq

/-- If color c was incident before vertex deletion, but is absent
afterward, the color-degree drops by at least one. -/
theorem incident_color_degree_strict_drop {V C : Type*}
    [DecidableEq V] [DecidableEq C]
    (E : V → V → C) {S T : Finset V}
    (hST : S ⊆ T) (x : V) (c : C)
    (hBefore : c ∈ incidentColors E T x)
    (hAfter : c ∉ incidentColors E S x) :
    incidentColorDegree E S x < incidentColorDegree E T x := by
  unfold incidentColorDegree
  have hsub := incident_colors_mono E hST x
  have hproper : incidentColors E S x ⊂ incidentColors E T x := by
    apply Finset.ssubset_iff_of_subset hsub |>.2
    exact ⟨c, hBefore, hAfter⟩
  exact Finset.card_lt_card hproper

end SchurFormal
