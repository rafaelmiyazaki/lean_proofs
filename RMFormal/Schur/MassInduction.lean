import Mathlib

/-!
# Strong induction on the remaining vertex count

A combinatorial weighted-deletion proof has two logical parts:
* find a proper induced subgraph whose mass is no smaller,
* apply induction to that smaller subgraph.

This theorem verifies the second part independently. The remaining
mathematical obligation in Lemma 2.1 is to construct the proper
weight-nondecreasing induced subgraph for every edge-colored graph.
-/

namespace SchurFormal

/-- A real-valued mass functional on finite vertex sets is at most
one if it is at most one on all sets of cardinality at most one,
and every larger set has a proper subset with no smaller mass. -/
theorem mass_le_one_by_strict_vertex_deletion
    {V : Type*} [DecidableEq V]
    (mass : Finset V → ℝ)
    (hBase : ∀ S : Finset V, S.card ≤ 1 → mass S ≤ 1)
    (hStep : ∀ S : Finset V, 2 ≤ S.card →
      ∃ T : Finset V, T ⊂ S ∧ mass S ≤ mass T)
    (U : Finset V) :
    mass U ≤ 1 := by
  have hInd : ∀ n : ℕ, ∀ S : Finset V,
      S.card = n → mass S ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hCard
      by_cases hSmall : n ≤ 1
      · exact hBase S (by omega)
      · obtain ⟨T, hProper, hMass⟩ := hStep S (by omega)
        have hTCard : T.card < n := by
          have h := Finset.card_lt_card hProper
          omega
        exact hMass.trans (ih T.card hTCard T rfl)
  exact hInd U.card U rfl

end SchurFormal
