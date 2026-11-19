import RMFormal.Schur.ColorDegrees

/-!
# Weighted choice of an incident edge color

This is the first selection step in the d≥2 case of Lemma 2.1.
The edges incident to v partition its neighbors by color. Therefore
some incident color accounts for at least a 1/d fraction of the
neighbor mass, where d is the number of incident colors at v.

No positivity assumption on the weights is needed for averaging.
-/

namespace SchurFormal

/-- A maximum-weight member of a nonempty finite index set has
at least the average weight. -/
theorem exists_large_finset_color
    {C : Type*} [DecidableEq C]
    (colors : Finset C) (hcolors : colors.Nonempty) (M : C → ℝ) :
    ∃ c ∈ colors,
      (∑ i ∈ colors, M i) ≤ (colors.card : ℝ) * M c := by
  by_contra hnone
  have hlt (c : C) (hc : c ∈ colors) :
      (colors.card : ℝ) * M c < ∑ i ∈ colors, M i := by
    by_contra h
    exact hnone ⟨c, hc, le_of_not_gt h⟩
  have hsum :
      (∑ c ∈ colors, (colors.card : ℝ) * M c) <
        ∑ c ∈ colors, (∑ i ∈ colors, M i) := by
    refine Finset.sum_lt_sum_of_nonempty hcolors ?_
    intro c hc
    exact hlt c hc
  have hleft :
      (∑ c ∈ colors, (colors.card : ℝ) * M c) =
        (colors.card : ℝ) * ∑ c ∈ colors, M c := by
    rw [Finset.mul_sum]
  have hright :
      (∑ c ∈ colors, (∑ i ∈ colors, M i)) =
        (colors.card : ℝ) * ∑ i ∈ colors, M i := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hleft, hright] at hsum
  exact lt_irrefl _ hsum

/-- Some incident edge color captures at least a 1/d share
of the total weight of neighbors, where d is the color-degree. -/
theorem exists_heavy_incident_color
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (U : Finset V) (v : V)
    (w : V → ℝ)
    (hcolors : (incidentColors E U v).Nonempty) :
    ∃ c ∈ incidentColors E U v,
      (∑ x ∈ U.erase v, w x) ≤
        (incidentColorDegree E U v : ℝ) *
          (∑ x ∈ U.erase v, if c = E v x then w x else 0) := by
  let colors := incidentColors E U v
  let M : C → ℝ :=
    fun c => ∑ x ∈ U.erase v, if c = E v x then w x else 0
  have hPartition : (∑ c ∈ colors, M c) =
      ∑ x ∈ U.erase v, w x := by
    dsimp [M]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    have hc : E v x ∈ colors :=
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    simp only [Finset.sum_ite_eq']
    simp [hc]
  obtain ⟨c, hc, hmax⟩ :=
    exists_large_finset_color colors hcolors M
  refine ⟨c, hc, ?_⟩
  simpa only [colors, M, incidentColorDegree] using
    (hPartition ▸ hmax)

end SchurFormal
