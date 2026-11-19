import RMFormal.Schur.ChargeColoring

/-!
# Paths in the difference graph and signed representations

A monochromatic walk of length n in the graph whose A-colored
edges are differences of elements of A yields a signed
representation with at most n terms. Combining this with the
verified charge-coloring theorem shows that every radius-m
difference-graph ball is properly (2m+1)-colorable in color A
when A avoids the target generalized Schur equation.

This formalization uses an inductively defined walk, with
repeated vertices and edges permitted (as in graph distance).
-/

namespace SchurFormal

/-- A walk in the undirected A-difference graph with exactly n edges. -/
inductive DifferencePath (A : Set ℕ) : ℕ → ℕ → ℕ → Prop
  | nil (a : ℕ) : DifferencePath A a a 0
  | snoc {a b c n : ℕ}
      (hp : DifferencePath A a b n)
      (hedge : DifferenceEdge A b c) :
      DifferencePath A a c (n + 1)

/-- An A-difference path gives a signed representation with one
    term for each step and the appropriate charge. -/
theorem differencePath_has_short_rep
    {A : Set ℕ} {a x n : ℕ}
    (hp : DifferencePath A a x n) :
    ∃ t : ℤ, HasShortSignedRep A a x n t := by
  induction hp with
  | nil =>
    refine ⟨0, [], [], ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      simp at hz
    · intro z hz
      simp at hz
    · simp
    · simp
    · simp
  | snoc hprev hedge ih =>
    rename_i b c stepN
    obtain ⟨t, ps, ns, hps, hns, hlen, hcharge, hsum⟩ := ih
    rcases hedge with ⟨hbc, hA⟩ | ⟨hcb, hA⟩
    · refine ⟨t + 1, (c - b) :: ps, ns, ?_, ?_, ?_, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with hw | hw
        · subst w
          exact hA
        · exact hps w hw
      · exact hns
      · simp only [List.length_cons]
        omega
      · simp only [List.length_cons]
        omega
      · simp only [List.sum_cons]
        omega
    · refine ⟨t - 1, ps, (b - c) :: ns, ?_, ?_, ?_, ?_, ?_⟩
      · exact hps
      · intro w hw
        rcases List.mem_cons.mp hw with hw | hw
        · subst w
          exact hA
        · exact hns w hw
      · simp only [List.length_cons]
        omega
      · simp only [List.length_cons]
        omega
      · simp only [List.sum_cons]
        omega

/-- Monochromatic reachability within radius m from base a. -/
def WithinDifferenceRadius (A : Set ℕ) (a m x : ℕ) : Prop :=
  ∃ n : ℕ, n ≤ m ∧ DifferencePath A a x n

private theorem signed_rep_mono
    {A : Set ℕ} {a x n m : ℕ} {t : ℤ}
    (hn : n ≤ m)
    (hrep : HasShortSignedRep A a x n t) :
    HasShortSignedRep A a x m t := by
  rcases hrep with ⟨ps, ns, hps, hns, hlen, hcharge, hsum⟩
  exact ⟨ps, ns, hps, hns, by omega, hcharge, hsum⟩

/-- A radius-m ball of the A-difference graph admits a
    proper (2m+1)-coloring of its A-colored edges. -/
theorem radius_ball_charge_coloring
    {A : Set ℕ} {a m : ℕ}
    (havoid : ¬ HasEquation A (m + 1) m) :
    ∃ color :
      {x : ℕ // WithinDifferenceRadius A a m x} → Fin (2 * m + 1),
      ∀ x y : {x : ℕ // WithinDifferenceRadius A a m x},
        DifferenceEdge A x.1 y.1 → color x ≠ color y := by
  apply reachable_has_charge_coloring
    (U := {x : ℕ | WithinDifferenceRadius A a m x})
    (A := A) (a := a)
  · intro x hx
    rcases hx with ⟨n, hn, hp⟩
    obtain ⟨t, ht⟩ := differencePath_has_short_rep hp
    exact ⟨t, signed_rep_mono hn ht⟩
  · exact havoid

end SchurFormal
