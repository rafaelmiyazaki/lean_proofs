import RMFormal.Schur.HeavyIndependentClass
import RMFormal.Schur.DegreeOneStar
import RMFormal.Schur.ProperDeletion
import RMFormal.Schur.WeightMassInductionStep

/-!
# Weighted local-coloring Lemma 2.1: the d=1 deletion step

Suppose a finite edge-colored complete graph has a vertex of
incident color-degree one, incident only with color c.
If the c-colored subgraph has a proper chi-coloring,
a maximum-mass color class P is independent and has
at least 1/chi of the total mass. Retaining P:
* strictly reduces the number of vertices, and
* does not decrease the total exact real vertex weight.

This is Case 1 of the paper's inductive Lemma 2.1, with
the local chromatic hypothesis supplied as an explicit
proper coloring. The d>=2 branch remains separate.
-/

namespace SchurFormal

theorem degree_one_mass_preserving_induced_subgraph
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C)
    (hSym : ∀ x y : V, E x y = E y x)
    (chi ell : ℕ) (hchi : 0 < chi) (hell : 0 < ell)
    (v y : V) (hne : v ≠ y)
    (hDegree : incidentColorDegree E Finset.univ v = 1)
    (c : C) (hColor : E v y = c)
    (col : V → Fin chi)
    (hProper : ∀ x y : V, x ≠ y →
      E x y = c → col x ≠ col y) :
    ∃ P : Finset V,
      P ⊂ Finset.univ ∧
      (∑ x ∈ (Finset.univ : Finset V),
        graphVertexWeight E chi ell Finset.univ x) ≤
      ∑ x ∈ P, graphVertexWeight E chi ell P x := by
  classical
  let w : V → ℝ :=
    fun x => graphVertexWeight E chi ell Finset.univ x
  obtain ⟨P, hPSub, hIndep, hHeavy⟩ :=
    exists_heavy_independent_class E c Finset.univ chi hchi
      col (by
        intro x _ y _ hxy hcx
        exact hProper x y hxy hcx)
      w
  have hPProper : P ⊂ (Finset.univ : Finset V) := by
    apply independent_class_proper E c Finset.univ P hPSub v y
      (Finset.mem_univ _) (Finset.mem_univ _)
      hne hColor hIndep
  have hIncident (x : V) (hx : x ∈ P) :
      c ∈ incidentColors E Finset.univ x := by
    by_cases hxv : x = v
    · subst x
      exact Finset.mem_image.mpr
        ⟨y, Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩,
          hColor⟩
    · have hvc : E v x = c := by
        have hu := incident_degree_one_uniform_star
          E Finset.univ v x y (by omega)
          (Finset.mem_univ _) (Finset.mem_univ _)
          hxv hne.symm
        exact hu.trans hColor
      have hxc : E x v = c := by
        rw [hSym x v]
        exact hvc
      exact Finset.mem_image.mpr
        ⟨v, Finset.mem_erase.mpr ⟨hxv.symm, Finset.mem_univ _⟩,
          hxc⟩
  have hPsubU : P ⊆ (Finset.univ : Finset V) := hPSub
  have hClosure :
      ∀ x ∈ P, ∀ z ∈ (Finset.univ : Finset V),
        E x z = c → z ∈ Finset.univ ∪ (∅ : Finset V) := by
    intro x hx z hz hc
    simp
  have hDrop : ∀ x ∈ P,
      incidentColorDegree E
        (keptAfterLayerDeletion Finset.univ Finset.univ ∅ P) x <
      incidentColorDegree E Finset.univ x := by
    intro x hx
    exact selected_color_degree_strictly_drops E
      Finset.univ Finset.univ ∅ P c hPsubU
      hClosure hIndep x hx (hIncident x hx)
  have hMinDegree : ∀ x ∈ P, 1 ≤ incidentColorDegree E Finset.univ x := by
    intro x hx
    have hpos : 0 < incidentColorDegree E Finset.univ x :=
      Finset.card_pos.mpr ⟨c, hIncident x hx⟩
    omega
  have hMass :
      (∑ x ∈ (Finset.univ : Finset V), w x) ≤
      ∑ x ∈ keptAfterLayerDeletion Finset.univ Finset.univ ∅ P,
        graphVertexWeight E chi ell
          (keptAfterLayerDeletion Finset.univ Finset.univ ∅ P) x := by
    apply weighted_graph_deletion_preserves_mass E chi ell 1 hchi hell
      Finset.univ Finset.univ ∅ P
      (Finset.Subset.refl _) (by simp) (by simp)
      hPsubU 1 (by norm_num) (by simp)
      hDrop hMinDegree
    · simp
    · simpa only [w] using hHeavy
  refine ⟨P, hPProper, ?_⟩
  simpa [w, keptAfterLayerDeletion] using hMass

end SchurFormal
