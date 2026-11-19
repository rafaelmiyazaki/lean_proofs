import RMFormal.Schur.DegreeOneMassStep
import RMFormal.Schur.DegreeGeTwoMassStep

/-!
# Universal strict weighted deletion for a finite vertex type

Combine the two minimum-color-degree cases in weighted Lemma 2.1:
d=1 and d>=2. For every finite symmetric edge-coloring with
local proper chi-colorings of all radius-i monochromatic balls,
the complete graph on V has a strictly smaller induced graph
with no smaller total exact vertex weight.

The final step for the paper's full Lemma 2.1 will be to inherit
the local hypothesis under arbitrary induced subgraphs, and
apply the already verified strong induction / cardinality bound.
-/

namespace SchurFormal

theorem complete_graph_mass_preserving_deletion
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C)
    (hSym : ∀ x y : V, E x y = E y x)
    (chi ell : ℕ) (hchi : 0 < chi) (hell : 0 < ell)
    (hV : 2 ≤ (Finset.univ : Finset V).card)
    (hLocal : ∀ (v : V) (c : C) (i : ℕ),
      1 ≤ i → i ≤ ell →
      ∃ color : V → Fin chi,
        ∀ x ∈ singleColorBall E c v i,
        ∀ y ∈ singleColorBall E c v i,
          x ≠ y → E x y = c → color x ≠ color y) :
    ∃ K : Finset V, K ⊂ Finset.univ ∧
      (∑ x ∈ (Finset.univ : Finset V),
        graphVertexWeight E chi ell Finset.univ x) ≤
      ∑ x ∈ K, graphVertexWeight E chi ell K x := by
  classical
  obtain ⟨v, hv, hdpos, hmin⟩ :=
    exists_min_incident_color_degree E Finset.univ hV
  by_cases hdOne : incidentColorDegree E Finset.univ v = 1
  · have hNonempty : (incidentColors E Finset.univ v).Nonempty :=
      Finset.card_pos.mp hdpos
    obtain ⟨c, hc⟩ := hNonempty
    obtain ⟨y, hyErase, hColor⟩ := Finset.mem_image.mp hc
    have hne : v ≠ y := by
      intro hvy
      exact (Finset.mem_erase.mp hyErase).1 hvy.symm
    obtain ⟨col, hProperBall⟩ :=
      hLocal v c 1 (by omega) (by omega)
    have hBall : singleColorBall E c v 1 = Finset.univ :=
      degree_one_color_ball_is_univ E v y
        (Finset.mem_erase.mp hyErase).1 hdOne c hColor
    have hProperAll : ∀ x y : V,
        x ≠ y → E x y = c → col x ≠ col y := by
      intro x y hxy hcx
      have hx : x ∈ singleColorBall E c v 1 := by
        rw [hBall]
        exact Finset.mem_univ _
      have hy : y ∈ singleColorBall E c v 1 := by
        rw [hBall]
        exact Finset.mem_univ _
      exact hProperBall x hx y hy hxy hcx
    exact degree_one_mass_preserving_induced_subgraph E hSym
      chi ell hchi hell v y hne hdOne c hColor col hProperAll
  · have hMinTwo : ∀ x : V, 2 ≤ incidentColorDegree E Finset.univ x := by
      intro x
      have hx := hmin x (Finset.mem_univ _)
      omega
    exact degree_ge_two_mass_preserving_induced_subgraph E hSym
      chi ell hchi hell hV hMinTwo hLocal

end SchurFormal
