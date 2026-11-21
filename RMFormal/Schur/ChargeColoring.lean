import RMFormal.Schur.ChargeClasses

/-!
# Coloring reachable vertices by their charge

This is the explicit (2m+1)-coloring construction used in
Section 3. The domain is any vertex set U for which every
vertex admits a short signed representation from a fixed base.
The conclusion says that every edge whose difference lies in A
has endpoints of distinct charge colors.

The separate graph-theoretic task still remaining is to show
that the radius-m ball in the difference-colored complete graph
satisfies the representation hypothesis.
-/

namespace SchurFormal

/-- Undirected difference edge colored by the class A.
    The strict inequality excludes loops. -/
def DifferenceEdge (A : Set ℕ) (x y : ℕ) : Prop :=
  (x < y ∧ y - x ∈ A) ∨ (y < x ∧ x - y ∈ A)

private theorem charge_bounds
    {A : Set ℕ} {a x m : ℕ} {t : ℤ}
    (h : HasShortSignedRep A a x m t) :
    0 ≤ t + (m : ℤ) ∧
    t + (m : ℤ) < ((2 * m + 1 : ℕ) : ℤ) := by
  rcases h with ⟨ps, ns, _, _, hshort, hcharge, _⟩
  omega

/-- An explicitly bounded charge index. -/
private def charge_index (m : ℕ) (t : ℤ)
    (hlo : 0 ≤ t + (m : ℤ))
    (hhi : t + (m : ℤ) < ((2 * m + 1 : ℕ) : ℤ)) :
    Fin (2 * m + 1) :=
  ⟨(t + (m : ℤ)).toNat, by
    have ht := Int.toNat_of_nonneg hlo
    omega⟩

/-- Each reachable set can be properly colored with at most
    2m+1 colors when edges are given by A-differences and
    A avoids the equation with lengths m+1 and m. -/
theorem reachable_has_charge_coloring
    {A U : Set ℕ} {a m : ℕ}
    (hcover : ∀ x ∈ U, ∃ t : ℤ, HasShortSignedRep A a x m t)
    (havoid : ¬ HasEquation A (m + 1) m) :
    ∃ color : U → Fin (2 * m + 1),
      ∀ x y : U, DifferenceEdge A x.1 y.1 →
        color x ≠ color y := by
  classical
  let t : U → ℤ := fun x => Classical.choose (hcover x.1 x.2)
  have ht (x : U) : HasShortSignedRep A a x.1 m (t x) :=
    Classical.choose_spec (hcover x.1 x.2)
  let color : U → Fin (2 * m + 1) :=
    fun x => charge_index m (t x)
      (charge_bounds (ht x)).1
      (charge_bounds (ht x)).2
  have hcolor_inj_charge (x y : U)
      (heq : color x = color y) : t x = t y := by
    have hval := congrArg Fin.val heq
    change (t x + (m : ℤ)).toNat =
      (t y + (m : ℤ)).toNat at hval
    have hx := (charge_bounds (ht x)).1
    have hy := (charge_bounds (ht y)).1
    have hxc := Int.toNat_of_nonneg hx
    have hyc := Int.toNat_of_nonneg hy
    omega
  refine ⟨color, ?_⟩
  intro x y hed heq
  have htxy : t x = t y := hcolor_inj_charge x y heq
  have hyrep : HasShortSignedRep A a y.1 m (t x) := by
    rw [htxy]
    exact ht y
  rcases hed with hxy | hyx
  · have heq' : y.1 = x.1 + (y.1 - x.1) := by omega
    exact havoid (same_charge_edge_creates_solution
      hyrep (ht x) hxy.2 heq')
  · have heq' : x.1 = y.1 + (x.1 - y.1) := by omega
    exact havoid (same_charge_edge_creates_solution
      (ht x) hyrep hyx.2 heq')

end SchurFormal
