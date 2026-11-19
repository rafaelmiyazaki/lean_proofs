import RMFormal.Schur.BezoutList

/-!
# The gcd-one case of the affine obstruction

If the gcd of a finite list of differences from a fixed base value
is one, then the represented set supports a generalized Schur solution.

This combines the finite Bezout algorithm with the verified
difference-certificate and sign-splitting lemmas.
-/

namespace SchurFormal

private lemma zip_support {A : Set ℕ} (vals : List ℕ) (cs : List ℤ)
    (hv : ∀ x ∈ vals, x ∈ A) :
    ∀ p ∈ vals.zip cs, p.1 ∈ A := by
  induction vals generalizing cs with
  | nil =>
    intro p hp
    simp at hp
  | cons x xs ih =>
    cases cs with
    | nil =>
      intro p hp
      simp at hp
    | cons c cs =>
      intro p hp
      rcases List.mem_cons.mp hp with hfirst | hrest
      · have hpx : p.1 = x := congrArg Prod.fst hfirst
        exact hpx.symm ▸ hv x (by simp)
      · exact ih cs (by
          intro y hy
          exact hv y (by simp [hy])) p hrest

private lemma zip_difference_sum (vals : List ℕ)
    (cs : List ℤ) (b : ℕ) :
    ((vals.zip cs).map (fun p =>
      p.2 * ((p.1 : ℤ) - (b : ℤ)))).sum =
      (List.zipWith (fun x c => x * c)
        (vals.map (fun x => (x : ℤ) - (b : ℤ))) cs).sum := by
  induction vals generalizing cs with
  | nil => simp
  | cons x xs ih =>
    cases cs with
    | nil => simp
    | cons c cs =>
      simp [List.zip, List.zipWith, ih, mul_comm]

/-- If the integer differences in a finite list have gcd one,
    they generate a generalized Schur equation. -/
theorem gcd_one_differences_force_solution
    {A : Set ℕ} (b : ℕ) (hb : b ∈ A)
    (vals : List ℕ) (hv : ∀ x ∈ vals, x ∈ A)
    (hgcd : integerListGcd
      (vals.map (fun x => (x : ℤ) - (b : ℤ))) = 1) :
    ∃ m : ℕ, 0 < m ∧ HasEquation A (m + 1) m := by
  obtain ⟨cs, _, hbez⟩ :=
    integerListGcd_bezout
      (vals.map (fun x => (x : ℤ) - (b : ℤ)))
  have hsum :
      (List.zipWith (fun x c => x * c)
        (vals.map (fun x => (x : ℤ) - (b : ℤ))) cs).sum = 1 := by
    simpa [hgcd] using hbez
  have hcertificate :
      ((vals.zip cs).map (fun p =>
        p.2 * ((p.1 : ℤ) - (b : ℤ)))).sum = 1 := by
    rw [zip_difference_sum]
    exact hsum
  exact difference_certificate_forces_solution
    b hb (vals.zip cs) Prod.fst Prod.snd
    (zip_support vals cs hv) hcertificate

end SchurFormal
