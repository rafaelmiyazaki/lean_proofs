import RMFormal.Schur.HeavySlowSelection
import RMFormal.Schur.ColorBallIncident
import RMFormal.Schur.HeavyIndependentClass
import RMFormal.Schur.ProperDeletion
import RMFormal.Schur.WeightMassInductionStep

/-!
# The minimum incident color-degree >=2 deletion branch

This is the assembly of the graph/mass construction of Case 2
in weighted Lemma 2.1, for the finite vertex type V.

Inputs: symmetric edge coloring, local proper chi-colorings of
every monochromatic radius-i ball (1<=i<=ell), and minimum
incident color-degree at least two.

Output: a strict induced vertex subset with no smaller
total exact real vertex weight.

The separate issue of applying this result to *each induced
subgraph* requires a restricted-walk/subtype formulation.
-/

namespace SchurFormal

theorem degree_ge_two_mass_preserving_induced_subgraph
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C)
    (hSym : ∀ x y : V, E x y = E y x)
    (chi ell : ℕ) (hchi : 0 < chi) (hell : 0 < ell)
    (hV : 2 ≤ (Finset.univ : Finset V).card)
    (hMinTwo : ∀ x : V, 2 ≤ incidentColorDegree E Finset.univ x)
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
  let w : V → ℝ :=
    fun x => graphVertexWeight E chi ell Finset.univ x
  have hw (x : V) : 0 < w x :=
    real_color_weight_pos chi ell
      (incidentColorDegree E Finset.univ x) hchi hell
  obtain ⟨v, c, hc, hdpos, hmin, hslowExists⟩ :=
    exists_heavy_slow_color_layer E w hV hw ell hell
  let d : ℕ := incidentColorDegree E Finset.univ v
  have hdTwo : 2 ≤ d := hMinTwo v
  obtain ⟨i, hi, hSlow⟩ := hslowExists hdTwo
  have hiLo : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hiUp : i ≤ ell := (Finset.mem_Icc.mp hi).2
  let S : Finset V := singleColorBall E c v i
  let T : Finset V :=
    singleColorBall E c v (i + 1) \ singleColorBall E c v i
  have hS : S ⊆ Finset.univ := Finset.subset_univ _
  have hT : T ⊆ Finset.univ := Finset.subset_univ _
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro x hxS hxT
    exact (Finset.mem_sdiff.mp hxT).2 hxS
  obtain ⟨color, hColorProper⟩ := hLocal v c i hiLo hiUp
  obtain ⟨P, hP, hIndependent, hHeavy⟩ :=
    exists_heavy_independent_class E c S chi hchi color
      (by
        intro x hx y hy hne hedge
        exact hColorProper x hx y hy hne hedge)
      w
  have hIncident (x : V) (hx : x ∈ P) :
      c ∈ incidentColors E Finset.univ x := by
    exact incident_color_of_ball E c v hSym hc i x
      (hP hx)
  have hDrop : ∀ x ∈ P,
      incidentColorDegree E
        (keptAfterLayerDeletion Finset.univ S T P) x <
      incidentColorDegree E Finset.univ x := by
    intro x hx
    apply selected_color_degree_strictly_drops E
      Finset.univ S T P c (hP.trans hS)
        ?_ hIndependent x hx (hIncident x hx)
    intro z hz y _ hzy
    exact single_color_neighbor_in_ball_or_layer E c v z y i
      (hP hz) hzy
  have hDMin : ∀ x ∈ P, d ≤ incidentColorDegree E Finset.univ x := by
    intro x hx
    exact hmin x
  let alpha : ℝ := (d : ℝ) ^ (1 / (ell : ℝ))
  have hAlpha : 1 ≤ alpha :=
    color_degree_root_ge_one d ell (by omega) hell
  let K := keptAfterLayerDeletion Finset.univ S T P
  have hMass :
      (∑ x ∈ (Finset.univ : Finset V), w x) ≤
        ∑ x ∈ K, graphVertexWeight E chi ell K x := by
    exact weighted_graph_deletion_preserves_mass E chi ell d
      hchi hell Finset.univ S T P hS hT hST hP
      alpha hAlpha (le_refl _) hDrop hDMin
      (by simpa only [T, S, w, colorBallMass, alpha, d] using hSlow)
      (by simpa only [S, w] using hHeavy)
  obtain ⟨y, hyErase, hyCol⟩ := Finset.mem_image.mp hc
  have hyNe : v ≠ y := by
    intro hvy
    exact (Finset.mem_erase.mp hyErase).1 hvy.symm
  have hPproper : P ⊂ S :=
    radius_ball_independent_class_proper E c v y i hiLo
      hyNe hyCol P hP hIndependent
  have hKproper : K ⊂ Finset.univ :=
    deletion_strictly_reduces_vertex_set Finset.univ S T P
      hS hPproper
  exact ⟨K, hKproper, by simpa only [w] using hMass⟩

end SchurFormal
