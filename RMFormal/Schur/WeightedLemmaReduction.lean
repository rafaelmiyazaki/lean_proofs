import RMFormal.Schur.MassInduction
import RMFormal.Schur.FinalWeightBound
import RMFormal.Schur.WeightMassInductionStep

/-!
# Reduction of Lemma 2.1 to finding a mass-preserving deletion

For the exact real vertex weights, the empty graph has total
mass 0, and a singleton has total mass 1.

This module completes the strong induction and numerical
cardinality bound under ONE remaining structural hypothesis:
every induced graph with at least two vertices admits a proper
vertex subset whose exact weighted mass is no smaller.

The structural hypothesis is not asserted as a theorem here;
constructing that subset from the local chromatic hypotheses
is precisely the outstanding work in Lemma 2.1.
-/

namespace SchurFormal

/-- Exact total vertex mass for a colored induced graph. -/
noncomputable def totalGraphWeight
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (chi ell : ℕ) (U : Finset V) : ℝ :=
  ∑ x ∈ U, graphVertexWeight E chi ell U x

/-- Empty and one-vertex graphs have total mass at most one. -/
theorem total_graph_weight_small
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (chi ell : ℕ)
    (S : Finset V) (hSmall : S.card ≤ 1) :
    totalGraphWeight E chi ell S ≤ 1 := by
  have hUnique : ∀ {x y : V}, x ∈ S → y ∈ S → x = y :=
    Finset.card_le_one_iff.mp hSmall
  have hDegreeZero (x : V) (hx : x ∈ S) :
      incidentColorDegree E S x = 0 := by
    have hErase : S.erase x = ∅ := by
      apply Finset.ext
      intro y
      constructor
      · intro hy
        have hyne := (Finset.mem_erase.mp hy).1
        have hyS := (Finset.mem_erase.mp hy).2
        exact False.elim (hyne (hUnique hyS hx))
      · intro hy
        simp at hy
    simp [incidentColorDegree, incidentColors, hErase]
  have hWeightOne : ∀ x ∈ S, graphVertexWeight E chi ell S x = 1 := by
    intro x hx
    simp [graphVertexWeight, hDegreeZero x hx, realColorWeight]
  have hTotal : totalGraphWeight E chi ell S = (S.card : ℝ) := by
    unfold totalGraphWeight
    calc
      (∑ x ∈ S, graphVertexWeight E chi ell S x) =
          ∑ x ∈ S, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hWeightOne x hx
      _ = (S.card : ℝ) := by simp
  rw [hTotal]
  exact_mod_cast hSmall

/-- The **full numerical conclusion** of Lemma 2.1 is reduced
to the structural deletion-existence step for every induced
subgraph of U, without assuming any other missing algebra. -/
theorem weighted_local_bound_of_deletion_principle
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (U : Finset V)
    (chi ell q : ℕ) (hchi : 0 < chi) (hell : 0 < ell)
    (hLocal : ∀ x ∈ U, incidentColorDegree E U x ≤ q)
    (hStep : ∀ S : Finset V, S ⊆ U → 2 ≤ S.card →
      ∃ T : Finset V, T ⊂ S ∧
        totalGraphWeight E chi ell S ≤ totalGraphWeight E chi ell T) :
    (U.card : ℝ) ≤ (chi : ℝ) ^ q *
      (Nat.factorial q : ℝ) ^ (1 / (ell : ℝ)) := by
  have hInd : ∀ n : ℕ, ∀ S : Finset V,
      S ⊆ U → S.card = n → totalGraphWeight E chi ell S ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hS hCard
      by_cases hSmall : n ≤ 1
      · exact total_graph_weight_small E chi ell S (by omega)
      · obtain ⟨T, hProper, hMass⟩ :=
          hStep S hS (by omega)
        have hTCard : T.card < n := by
          have hh := Finset.card_lt_card hProper
          omega
        have hTSub : T ⊆ U := hProper.subset.trans hS
        exact hMass.trans (ih T.card hTCard T hTSub rfl)
  have hMass : totalGraphWeight E chi ell U ≤ 1 :=
    hInd U.card U (Finset.Subset.refl U) rfl
  exact count_bound_of_total_vertex_mass E U chi ell q hchi hell
    hLocal (by simpa [totalGraphWeight, graphVertexWeight] using hMass)

end SchurFormal
