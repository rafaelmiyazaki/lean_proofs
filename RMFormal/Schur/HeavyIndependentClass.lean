import RMFormal.Schur.HeavyClass

/-!
# Weighted independent color class

Turn a proper chi-coloring of one monochromatic subgraph into
an independent vertex class containing at least 1/chi of its
total weight. This is the selection step in both cases of
the weighted local-coloring Lemma 2.1.

The result works with arbitrary real vertex weights;
their positivity is not needed for the averaging statement.
-/

namespace SchurFormal

theorem exists_heavy_independent_class
    {V C : Type*} [DecidableEq V]
    (E : V → V → C) (c : C) (U : Finset V)
    (chi : ℕ) (hchi : 0 < chi)
    (color : V → Fin chi)
    (hproper : ∀ x ∈ U, ∀ y ∈ U,
      x ≠ y → E x y = c → color x ≠ color y)
    (w : V → ℝ) :
    ∃ P : Finset V,
      P ⊆ U ∧
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y → E x y ≠ c) ∧
      (∑ x ∈ U, w x) ≤ (chi : ℝ) * (∑ x ∈ P, w x) := by
  classical
  let M : Fin chi → ℝ :=
    fun i => ∑ x ∈ U, if color x = i then w x else 0
  have hPartition : (∑ i : Fin chi, M i) = ∑ x ∈ U, w x := by
    dsimp [M]
    calc
      (∑ i : Fin chi, ∑ x ∈ U, if color x = i then w x else 0) =
          ∑ x ∈ U, ∑ i : Fin chi, if color x = i then w x else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ x ∈ U, w x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp
  obtain ⟨i, hi⟩ := exists_color_with_large_weight chi hchi M
  let P : Finset V := U.filter (fun x => color x = i)
  refine ⟨P, ?_, ?_, ?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).1
  · intro x hx y hy hne hedge
    have hxU := (Finset.mem_filter.mp hx).1
    have hyU := (Finset.mem_filter.mp hy).1
    have hxColor := (Finset.mem_filter.mp hx).2
    have hyColor := (Finset.mem_filter.mp hy).2
    have hneq := hproper x hxU y hyU hne hedge
    exact hneq (hxColor.trans hyColor.symm)
  · rw [hPartition] at hi
    simpa [P, M, Finset.sum_filter] using hi

end SchurFormal
