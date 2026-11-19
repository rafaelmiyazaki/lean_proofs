import RMFormal.Schur.ColorDeletion

/-!
# Color-graph balls and their next layer

This constructs the graph objects from the weighted induction
in Lemma 2.1. A color-c neighbor of a vertex in the radius-i
ball belongs either to the same ball or to the next layer.
The statement holds for any finite edge-colored graph
(we need not assume the graph is complete or the edge-color
function symmetric for this direction).

The result supplies the closure condition used in
ColorDeletion.lean.
-/

namespace SchurFormal

/-- A walk with n edges of color c, allowing repeated vertices. -/
inductive SingleColorWalk {V C : Type*} (E : V → V → C) (c : C) :
    V → V → ℕ → Prop
  | nil (a : V) : SingleColorWalk E c a a 0
  | snoc {a b d : V} {n : ℕ}
      (hprev : SingleColorWalk E c a b n)
      (hcolor : E b d = c) :
      SingleColorWalk E c a d (n + 1)

/-- The radius-i ball of the directed color-c graph. -/
def WithinSingleColorRadius {V C : Type*}
    (E : V → V → C) (c : C) (a : V) (i : ℕ) (x : V) : Prop :=
  ∃ n : ℕ, n ≤ i ∧ SingleColorWalk E c a x n

theorem within_single_color_radius_extend {V C : Type*}
    (E : V → V → C) (c : C) (a x y : V) (i : ℕ)
    (hx : WithinSingleColorRadius E c a i x)
    (hxy : E x y = c) :
    WithinSingleColorRadius E c a (i + 1) y := by
  rcases hx with ⟨n, hn, hp⟩
  exact ⟨n + 1, by omega, SingleColorWalk.snoc hp hxy⟩

/-- The finite vertex set reached in at most i steps in color c. -/
noncomputable def singleColorBall
    {V C : Type*} [Fintype V]
    (E : V → V → C) (c : C) (a : V) (i : ℕ) : Finset V :=
  Finset.univ.filter (WithinSingleColorRadius E c a i)

/-- Every color-c neighbor of a vertex within distance i
lies in the radius-i ball or the next layer. -/
theorem single_color_neighbor_in_ball_or_layer
    {V C : Type*} [Fintype V]
    (E : V → V → C) (c : C) (a x y : V) (i : ℕ)
    (hx : x ∈ singleColorBall E c a i)
    (hxy : E x y = c) :
    y ∈ singleColorBall E c a i ∪
      (singleColorBall E c a (i + 1) \
        singleColorBall E c a i) := by
  classical
  have hr : WithinSingleColorRadius E c a i x :=
    (Finset.mem_filter.mp hx).2
  have hyNext : y ∈ singleColorBall E c a (i + 1) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, within_single_color_radius_extend
      E c a x y i hr hxy⟩
  by_cases hy : y ∈ singleColorBall E c a i
  · exact Finset.mem_union.mpr (Or.inl hy)
  · exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_sdiff.mpr ⟨hyNext, hy⟩))

end SchurFormal
