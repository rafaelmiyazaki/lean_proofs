import RMFormal.Schur.ColorDeletion

/-!
# Strict vertex reduction for the weighted induction

Selecting a proper independent subset P of a ball S and retaining
only P outside the removed layer produces a strictly smaller
induced vertex set. This is the combinatorial termination measure
needed in the induction for the weighted local-coloring lemma.
-/

namespace SchurFormal

/-- Any vertex of S that is not retained in P has been deleted. -/
theorem removed_ball_vertex_not_kept
    {V : Type*} [DecidableEq V]
    (U S T P : Finset V) (v : V)
    (hvS : v ∈ S) (hvP : v ∉ P) :
    v ∉ keptAfterLayerDeletion U S T P := by
  intro hv
  rcases Finset.mem_union.mp hv with hOutside | hSelected
  · exact (Finset.mem_sdiff.mp hOutside).2
      (Finset.mem_union.mpr (Or.inl hvS))
  · exact hvP hSelected

/-- If S contains a vertex outside P, the kept induced graph
has strictly fewer vertices than the original U. -/
theorem kept_card_lt_of_unselected_vertex
    {V : Type*} [DecidableEq V]
    (U S T P : Finset V)
    (hP : P ⊆ U) (v : V)
    (hvU : v ∈ U) (hvS : v ∈ S) (hvP : v ∉ P) :
    (keptAfterLayerDeletion U S T P).card < U.card := by
  have hsub : keptAfterLayerDeletion U S T P ⊆ U :=
    kept_vertices_subset hP
  have hproper : keptAfterLayerDeletion U S T P ⊂ U := by
    apply Finset.ssubset_iff_of_subset hsub |>.2
    exact ⟨v, hvU, removed_ball_vertex_not_kept U S T P v hvS hvP⟩
  exact Finset.card_lt_card hproper

/-- A nontrivial monochromatic edge inside S ensures that any
independent P⊆S misses at least one endpoint. -/
theorem kept_card_lt_of_independent_class
    {V C : Type*} [DecidableEq V]
    (E : V → V → C) (U S T P : Finset V) (c : C)
    (hS : S ⊆ U) (hP : P ⊆ S)
    (x y : V) (hx : x ∈ S) (hy : y ∈ S)
    (hne : x ≠ y) (hEdge : E x y = c)
    (hIndependent : ∀ u ∈ P, ∀ v ∈ P,
      u ≠ v → E u v ≠ c) :
    (keptAfterLayerDeletion U S T P).card < U.card := by
  by_cases hxP : x ∈ P
  · have hyP : y ∉ P := by
      intro hyP
      exact hIndependent x hxP y hyP hne hEdge
    exact kept_card_lt_of_unselected_vertex U S T P
      (Finset.Subset.trans hP hS) y (hS hy) hy hyP
  · exact kept_card_lt_of_unselected_vertex U S T P
      (Finset.Subset.trans hP hS) x (hS hx) hx hxP

end SchurFormal
