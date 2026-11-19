import RMFormal.Schur.InducedWeightTransport

/-!
# Discharging the universal induced-deletion obligation

The full weighted local-coloring induction requires the
mass-preserving deletion lemma on EVERY induced vertex set, not
just the original graph. Represent any vertex set S by its
finite subtype and apply complete_graph_mass_preserving_deletion.
Transport the resulting subgraph and its exact weights back to S.

No additional graph-theoretic hypothesis is introduced: the
local coloring assumption is inherited by induced subgraphs
using the verified walk-lifting theorem.
-/

namespace SchurFormal

theorem mass_preserving_deletion_on_every_induced_set
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C)
    (hSym : ∀ x y : V, E x y = E y x)
    (chi ell : ℕ) (hchi : 0 < chi) (hell : 0 < ell)
    (hLocal : ∀ (v : V) (c : C) (i : ℕ),
      1 ≤ i → i ≤ ell →
      ∃ color : V → Fin chi,
        ∀ x ∈ singleColorBall E c v i,
        ∀ y ∈ singleColorBall E c v i,
          x ≠ y → E x y = c → color x ≠ color y)
    (S : Finset V) (hCard : 2 ≤ S.card) :
    ∃ T : Finset V, T ⊂ S ∧
      (∑ x ∈ S, graphVertexWeight E chi ell S x) ≤
        ∑ x ∈ T, graphVertexWeight E chi ell T x := by
  classical
  let ES : {x : V // x ∈ S} → {x : V // x ∈ S} → C :=
    inducedEdgeColors E
  have hSymS : ∀ x y : {x : V // x ∈ S}, ES x y = ES y x := by
    intro x y
    exact hSym x.1 y.1
  have hLocalS :
      ∀ (v : {x : V // x ∈ S}) (c : C) (i : ℕ),
      1 ≤ i → i ≤ ell →
      ∃ color : {x : V // x ∈ S} → Fin chi,
        ∀ x ∈ singleColorBall ES c v i,
        ∀ y ∈ singleColorBall ES c v i,
          x ≠ y → ES x y = c → color x ≠ color y :=
    induced_local_colorability E S chi ell hLocal
  have hSubtypeCard :
      2 ≤ (Finset.univ : Finset {x : V // x ∈ S}).card := by
    simpa [Fintype.card_coe] using hCard
  obtain ⟨T', hProper', hMass'⟩ :=
    complete_graph_mass_preserving_deletion ES hSymS
      chi ell hchi hell hSubtypeCard hLocalS
  let T : Finset V := T'.image Subtype.val
  have hTsub : T ⊆ S := by
    intro x hx
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
    exact z.2
  have hProper : T ⊂ S := by
    apply (Finset.ssubset_iff_of_subset hTsub).2
    obtain ⟨z, _, hzNot⟩ :=
      (Finset.ssubset_iff_of_subset hProper'.subset).1 hProper'
    refine ⟨z.1, z.2, ?_⟩
    intro hzT
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hzT
    have hUEq : u = z := Subtype.ext heq
    subst u
    exact hzNot hu
  have hOld := induced_mass_image E S
    (Finset.univ : Finset {x : V // x ∈ S}) chi ell
  rw [subtype_finset_image_univ S] at hOld
  have hNew := induced_mass_image E S T' chi ell
  have hMass :
      (∑ x ∈ S, graphVertexWeight E chi ell S x) ≤
        ∑ x ∈ T, graphVertexWeight E chi ell T x := by
    calc
      _ = ∑ z ∈ (Finset.univ : Finset {x : V // x ∈ S}),
            graphVertexWeight ES chi ell Finset.univ z := hOld.symm
      _ ≤ ∑ z ∈ T', graphVertexWeight ES chi ell T' z := hMass'
      _ = ∑ x ∈ T, graphVertexWeight E chi ell T x := by
        simpa only [ES, T] using hNew
  exact ⟨T, hProper, hMass⟩

/-- Full weighted local-coloring bound from the local
monochromatic-radius coloring hypotheses. -/
theorem weighted_local_bound_from_local_colorings
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C)
    (hSym : ∀ x y : V, E x y = E y x)
    (U : Finset V)
    (chi ell q : ℕ) (hchi : 0 < chi) (hell : 0 < ell)
    (hDegree : ∀ x ∈ U, incidentColorDegree E U x ≤ q)
    (hLocal : ∀ (v : V) (c : C) (i : ℕ),
      1 ≤ i → i ≤ ell →
      ∃ color : V → Fin chi,
        ∀ x ∈ singleColorBall E c v i,
        ∀ y ∈ singleColorBall E c v i,
          x ≠ y → E x y = c → color x ≠ color y) :
    (U.card : ℝ) ≤ (chi : ℝ) ^ q *
      (Nat.factorial q : ℝ) ^ (1 / (ell : ℝ)) := by
  apply weighted_local_bound_of_deletion_principle E U
    chi ell q hchi hell hDegree
  intro S hSub hCard
  exact mass_preserving_deletion_on_every_induced_set E hSym
    chi ell hchi hell hLocal S hCard

end SchurFormal
