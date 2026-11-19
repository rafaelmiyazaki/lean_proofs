import RMFormal.Schur.AllCasesDeletion

/-!
# Inheritance of monochromatic radius-ball colorability

For a finite induced vertex type {x // x ∈ S}, every
monochromatic walk lifts to a walk in the original graph.
Consequently every induced monochromatic radius ball lies inside
the corresponding original graph ball.

The local proper chi-coloring hypothesis of Lemma 2.1 is
therefore hereditary under passage to induced subgraphs.
-/

namespace SchurFormal

/-- The coloring obtained by restricting E to a vertex subset. -/
def inducedEdgeColors
    {V C : Type*} {S : Finset V} (E : V → V → C) :
    {x : V // x ∈ S} → {x : V // x ∈ S} → C :=
  fun x y => E x.1 y.1

/-- A monochromatic walk in an induced graph lifts verbatim
to the original edge-colored graph. -/
theorem induced_single_color_walk_lifts
    {V C : Type*} {S : Finset V}
    (E : V → V → C) (c : C)
    {a x : {y : V // y ∈ S}} {n : ℕ}
    (hp : SingleColorWalk (inducedEdgeColors E) c a x n) :
    SingleColorWalk E c a.1 x.1 n := by
  induction hp with
  | nil =>
    exact SingleColorWalk.nil _
  | snoc hprev hedge ih =>
    exact SingleColorWalk.snoc ih hedge

/-- Every vertex reached in the induced graph belongs to
the analogous radius ball of the original graph. -/
theorem induced_ball_subset_original
    {V C : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → C) (S : Finset V) (c : C)
    (a x : {z : V // z ∈ S}) (i : ℕ)
    (hx : x ∈ singleColorBall (inducedEdgeColors E) c a i) :
    x.1 ∈ singleColorBall E c a.1 i := by
  classical
  have hReach : WithinSingleColorRadius
      (inducedEdgeColors E) c a i x := by
    unfold singleColorBall at hx
    exact (Finset.mem_filter.mp hx).2
  obtain ⟨n, hn, hp⟩ := hReach
  unfold singleColorBall
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨n, hn,
      induced_single_color_walk_lifts E c hp⟩⟩

/-- Restriction preserves proper local monochromatic colorability
for every radius between 1 and ell. -/
theorem induced_local_colorability
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (S : Finset V)
    (chi ell : ℕ)
    (hLocal : ∀ (v : V) (c : C) (i : ℕ),
      1 ≤ i → i ≤ ell →
      ∃ color : V → Fin chi,
        ∀ x ∈ singleColorBall E c v i,
        ∀ y ∈ singleColorBall E c v i,
          x ≠ y → E x y = c → color x ≠ color y) :
    ∀ (v : {x : V // x ∈ S}) (c : C) (i : ℕ),
      1 ≤ i → i ≤ ell →
      ∃ color : {x : V // x ∈ S} → Fin chi,
        ∀ x ∈ singleColorBall (inducedEdgeColors E) c v i,
        ∀ y ∈ singleColorBall (inducedEdgeColors E) c v i,
          x ≠ y →
          inducedEdgeColors E x y = c →
          color x ≠ color y := by
  classical
  intro v c i hi1 hiEll
  obtain ⟨col, hproper⟩ := hLocal v.1 c i hi1 hiEll
  refine ⟨fun x => col x.1, ?_⟩
  intro x hx y hy hne hxy
  have hxOriginal : x.1 ∈ singleColorBall E c v.1 i :=
    induced_ball_subset_original E S c v x i hx
  have hyOriginal : y.1 ∈ singleColorBall E c v.1 i :=
    induced_ball_subset_original E S c v y i hy
  have hneVal : x.1 ≠ y.1 := by
    intro h
    exact hne (Subtype.ext h)
  exact hproper x.1 hxOriginal y.1 hyOriginal
    hneVal hxy

end SchurFormal
