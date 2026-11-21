import RMFormal.Schur.Padding
import RMFormal.Schur.Charge

/-!
# Charge classes for the difference-colored complete graph

The arithmetic heart of Section 3:
a short signed representation of x from a base a has
a + ps.sum = x + ns.sum. Two representations with the
same charge and endpoints joined by an A-colored edge
force a generalized Schur equation.

This makes the charge-class independence argument explicit
while allowing repeated summands.
-/

namespace SchurFormal

/-- A signed representation of x from base a with at most m steps
and prescribed charge, using terms only from A. -/
def HasShortSignedRep (A : Set ℕ) (a x m : ℕ) (t : ℤ) : Prop :=
  ∃ ps ns : List ℕ,
    (∀ z ∈ ps, z ∈ A) ∧
    (∀ z ∈ ns, z ∈ A) ∧
    ps.length + ns.length ≤ m ∧
    (ps.length : ℤ) - (ns.length : ℤ) = t ∧
    a + ps.sum = x + ns.sum

/-- Two same-charge short representations joined by an A-colored
edge give a monochromatic (m+1,m) equation. -/
theorem same_charge_edge_creates_solution
    {A : Set ℕ} {a x y z m : ℕ} {t : ℤ}
    (hx : HasShortSignedRep A a x m t)
    (hy : HasShortSignedRep A a y m t)
    (hz : z ∈ A)
    (hxy : x = y + z) :
    HasEquation A (m + 1) m := by
  rcases hx with ⟨ps, ns, hps, hns, hshort, hcharge, hsum⟩
  rcases hy with ⟨qs, rs, hqs, hrs, hshort', hcharge', hsum'⟩
  have hlength : ps.length + rs.length = ns.length + qs.length := by
    omega
  have hcross : z + ns.sum + qs.sum = ps.sum + rs.sum := by
    omega
  let k := ps.length + rs.length
  have hkbound : k ≤ m := by
    dsimp [k]
    omega
  have hshortsol : HasEquation A (k + 1) k := by
    refine ⟨z :: (ns ++ qs), ps ++ rs, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons, List.length_append]
      dsimp [k]
      omega
    · simp only [List.length_append]
      rfl
    · intro w hw
      rcases List.mem_cons.mp hw with hzw | hw
      · simpa [hzw] using hz
      · rcases List.mem_append.mp hw with h | h
        · exact hns w h
        · exact hqs w h
    · intro w hw
      rcases List.mem_append.mp hw with h | h
      · exact hps w h
      · exact hrs w h
    · simp only [List.sum_cons, List.sum_append]
      omega
  have hpad : HasEquation A (k + 1 + (m - k)) (k + (m - k)) := by
    simpa only [Nat.mul_one] using
      (padding_lemma_3_1 (A := A) (u := k + 1) (v := k)
        (by omega) hshortsol 1 (m - k))
  have hnorm : k + 1 + (m - k) = m + 1 ∧ k + (m - k) = m := by
    omega
  rw [hnorm.1, hnorm.2] at hpad
  exact hpad

/-- If A avoids the prescribed equation, no A-colored edge
joins two endpoints represented with the same charge. -/
theorem same_charge_no_edge
    {A : Set ℕ} {a x y z m : ℕ} {t : ℤ}
    (havoid : ¬ HasEquation A (m + 1) m)
    (hx : HasShortSignedRep A a x m t)
    (hy : HasShortSignedRep A a y m t)
    (hz : z ∈ A)
    (hxy : x = y + z) : False :=
  havoid (same_charge_edge_creates_solution hx hy hz hxy)

end SchurFormal
