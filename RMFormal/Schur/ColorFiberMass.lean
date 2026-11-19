import RMFormal.Schur.HeavyClass

/-!
# Maximal-weight color classes for the weighted graph lemma

This specializes the abstract averaging theorem to the fibers of
an actual coloring of a finite vertex type. The sum of masses
of the color fibers is exactly the total vertex mass.

The coloring need not be proper here; properness will be
supplied from the color-c subgraph in Lemma 2.1.
-/

namespace SchurFormal

/-- The weight of some fiber of any chi-coloring is at least
one chi-th of the total weight. -/
theorem exists_heavy_color_fiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (chi : ℕ) (hchi : 0 < chi)
    (color : V → Fin chi) (w : V → ℝ) :
    ∃ i : Fin chi,
      (∑ v : V, w v) ≤
        (chi : ℝ) * (∑ v : V, if color v = i then w v else 0) := by
  classical
  let M : Fin chi → ℝ :=
    fun i => ∑ v : V, if color v = i then w v else 0
  obtain ⟨i, hi⟩ := exists_color_with_large_weight chi hchi M
  have hPartition : (∑ i : Fin chi, M i) = ∑ v : V, w v := by
    dsimp [M]
    calc
      (∑ i : Fin chi, ∑ v : V, if color v = i then w v else 0) =
          ∑ v : V, ∑ i : Fin chi, if color v = i then w v else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ v : V, w v := by
        apply Finset.sum_congr rfl
        intro v _
        simp
  rw [hPartition] at hi
  exact ⟨i, hi⟩

end SchurFormal
