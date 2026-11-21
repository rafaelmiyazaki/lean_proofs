import RMFormal.Schur.InducedBallColoring
import RMFormal.Schur.WeightedLemmaReduction

/-!
# Exact incident-color-degree and vertex-weight transport to subtypes

When a vertex set S is represented by the finite subtype
{x // x ∈ S}, restricting the edge coloring has precisely the
same incident-color sets and factorial weights as the original
colored graph induced on S. This is needed to turn a
finite-type deletion proof into the global induction on Finset V.
-/

namespace SchurFormal

/-- Every finite subset of the subtype projects injectively. -/
theorem subtype_finset_image_univ
    {V : Type*} [DecidableEq V] (S : Finset V) :
    (Finset.univ : Finset {x : V // x ∈ S}).image Subtype.val = S := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
    exact z.2
  · intro hx
    exact Finset.mem_image.mpr
      ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩

/-- Incident colors agree under projection of an induced finite
subtype graph. -/
theorem induced_incident_colors_image
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (S : Finset V)
    (T : Finset {z : V // z ∈ S}) (x : {z : V // z ∈ S}) :
    incidentColors (inducedEdgeColors E) T x =
      incidentColors E (T.image Subtype.val) x.1 := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨y, hy, hcol⟩ := Finset.mem_image.mp hc
    have hyT : y ∈ T := (Finset.mem_erase.mp hy).2
    have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
    have hyneVal : y.1 ≠ x.1 := by
      intro h
      exact hyne (Subtype.ext h)
    have hyImg : y.1 ∈ T.image Subtype.val :=
      Finset.mem_image.mpr ⟨y, hyT, rfl⟩
    exact Finset.mem_image.mpr
      ⟨y.1, Finset.mem_erase.mpr ⟨hyneVal, hyImg⟩, hcol⟩
  · intro hc
    obtain ⟨y, hy, hcol⟩ := Finset.mem_image.mp hc
    have hyImg : y ∈ T.image Subtype.val :=
      (Finset.mem_erase.mp hy).2
    have hyne : y ≠ x.1 := (Finset.mem_erase.mp hy).1
    obtain ⟨z, hz, hval⟩ := Finset.mem_image.mp hyImg
    have hzne : z ≠ x := by
      intro heq
      exact hyne (hval.symm.trans (congrArg Subtype.val heq))
    have hzcol : inducedEdgeColors E x z = c := by
      change E x.1 z.1 = c
      rw [hval]
      exact hcol
    exact Finset.mem_image.mpr
      ⟨z, Finset.mem_erase.mpr ⟨hzne, hz⟩, hzcol⟩

theorem induced_incident_degree_image
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (S : Finset V)
    (T : Finset {z : V // z ∈ S}) (x : {z : V // z ∈ S}) :
    incidentColorDegree (inducedEdgeColors E) T x =
      incidentColorDegree E (T.image Subtype.val) x.1 := by
  unfold incidentColorDegree
  rw [induced_incident_colors_image E S T x]

theorem induced_weight_image
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (S : Finset V)
    (T : Finset {z : V // z ∈ S}) (x : {z : V // z ∈ S})
    (chi ell : ℕ) :
    graphVertexWeight (inducedEdgeColors E) chi ell T x =
      graphVertexWeight E chi ell (T.image Subtype.val) x.1 := by
  unfold graphVertexWeight
  rw [induced_incident_degree_image E S T x]

/-- The exact total real weight is invariant under treating
an induced graph as a finite subtype. -/
theorem induced_mass_image
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (S : Finset V)
    (T : Finset {z : V // z ∈ S})
    (chi ell : ℕ) :
    (∑ x ∈ T, graphVertexWeight (inducedEdgeColors E) chi ell T x) =
      ∑ x ∈ T.image Subtype.val,
        graphVertexWeight E chi ell (T.image Subtype.val) x := by
  classical
  calc
    _ = ∑ x ∈ T,
          graphVertexWeight E chi ell (T.image Subtype.val) x.1 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact induced_weight_image E S T x chi ell
    _ = ∑ x ∈ T.image Subtype.val,
          graphVertexWeight E chi ell (T.image Subtype.val) x := by
      rw [Finset.sum_image Subtype.val_injective.injOn]

end SchurFormal
