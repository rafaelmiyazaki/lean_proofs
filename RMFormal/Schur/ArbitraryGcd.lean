import RMFormal.Schur.GcdOne

/-!
# From a divisor of differences to a Schur equation

Generalizes the earlier certificate lemma:
a signed linear combination of differences equal to the
base point b (not necessarily 1) gives an affine relation.
-/

namespace SchurFormal

private lemma sum_neg_fst (xs : List (ℤ × ℕ)) :
    (xs.map (fun p => -p.1)).sum =
      -(xs.map Prod.fst).sum := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private lemma sum_neg_weight (xs : List (ℤ × ℕ)) :
    (xs.map (fun p => -p.1 * (p.2 : ℤ))).sum =
      -(xs.map (fun p => p.1 * (p.2 : ℤ))).sum := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private lemma sum_difference_weight (xs : List (ℤ × ℕ)) (b : ℕ) :
    (xs.map (fun p => p.1 * ((p.2 : ℤ) - (b : ℤ)))).sum =
      (xs.map (fun p => p.1 * (p.2 : ℤ))).sum -
        (b : ℤ) * (xs.map Prod.fst).sum := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

/-- A certificate expressing the base element itself as a
combination of differences yields an asymmetric Schur equation. -/
theorem base_difference_certificate_forces_solution
    {A : Set ℕ} (b : ℕ) (hb : b ∈ A)
    (xs : List (ℤ × ℕ))
    (hmem : ∀ p ∈ xs, p.2 ∈ A)
    (hcomb : (xs.map (fun p =>
      p.1 * ((p.2 : ℤ) - (b : ℤ)))).sum = (b : ℤ)) :
    ∃ m : ℕ, 0 < m ∧ HasEquation A (m + 1) m := by
  let pairs : List (ℤ × ℕ) :=
    (1 + (xs.map Prod.fst).sum, b) ::
       xs.map (fun p => (-p.1, p.2))
  have hpairs : ∀ p ∈ pairs, p.2 ∈ A := by
    intro p hp
    rcases List.mem_cons.mp hp with hfirst | hrest
    · have hpb : p.2 = b := congrArg Prod.snd hfirst
      exact hpb.symm ▸ hb
    · obtain ⟨q, hq, heq⟩ := List.mem_map.mp hrest
      have hpq : p.2 = q.2 := (congrArg Prod.snd heq).symm
      exact hpq.symm ▸ hmem q hq
  have hcount : (pairs.map Prod.fst).sum = 1 := by
    simp only [pairs, List.map_cons, List.sum_cons, List.map_map]
    change (1 + (xs.map Prod.fst).sum) +
      (xs.map (fun p => -p.1)).sum = 1
    rw [sum_neg_fst]
    ring
  have hweight :
      (pairs.map (fun p => p.1 * (p.2 : ℤ))).sum = 0 := by
    simp only [pairs, List.map_cons, List.sum_cons, List.map_map]
    change (1 + (xs.map Prod.fst).sum) * (b : ℤ) +
      (xs.map (fun p => -p.1 * (p.2 : ℤ))).sum = 0
    rw [sum_neg_weight]
    have hdiff := sum_difference_weight xs b
    nlinarith [hcomb, hdiff]
  exact affine_relation_forces_solution pairs Prod.snd Prod.fst
    hpairs hcount hweight

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

private lemma zip_difference_sum (vals : List ℕ) (cs : List ℤ) (b : ℕ) :
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
      simp [List.zip, List.zipWith, mul_comm]
      simpa [List.zip, List.zipWith, mul_comm] using ih cs

private lemma zipWith_scaled (xs cs : List ℤ) (q : ℤ) :
    (List.zipWith (fun x c => x * c) xs (cs.map (fun c => q*c))).sum =
      q * (List.zipWith (fun x c => x * c) xs cs).sum := by
  induction xs generalizing cs with
  | nil => simp
  | cons x xs ih =>
    cases cs with
    | nil => simp
    | cons c cs =>
      simp only [List.map_cons, List.zipWith, List.sum_cons]
      rw [ih cs]
      ring

/-- If the gcd of differences divides the base point,
    there is a generalized Schur solution (arbitrary gcd). -/
theorem gcd_differences_dvd_base_forces_solution
    {A : Set ℕ} (b : ℕ) (hb : b ∈ A)
    (vals : List ℕ) (hv : ∀ x ∈ vals, x ∈ A)
    (hdvd : ((integerListGcd
        (vals.map (fun x => (x : ℤ) - (b : ℤ))) : ℕ) : ℤ) ∣ (b : ℤ)) :
    ∃ m : ℕ, 0 < m ∧ HasEquation A (m + 1) m := by
  let ds := vals.map (fun x => (x : ℤ) - (b : ℤ))
  obtain ⟨cs, _, hbez⟩ := integerListGcd_bezout ds
  obtain ⟨q, hq⟩ := hdvd
  let scaled := cs.map (fun c => q * c)
  have hsum : (List.zipWith (fun x c => x*c) ds scaled).sum = (b : ℤ) := by
    change (List.zipWith (fun x c => x*c) ds
      (cs.map (fun c => q*c))).sum = (b : ℤ)
    rw [zipWith_scaled, hbez]
    simpa [mul_comm] using hq.symm
  have hcertificate :
      ((vals.zip scaled).map (fun p =>
        p.2 * ((p.1 : ℤ) - (b : ℤ)))).sum = (b : ℤ) := by
    rw [zip_difference_sum]
    exact hsum
  exact base_difference_certificate_forces_solution b hb
    ((vals.zip scaled).map fun p => (p.2,p.1))
    (by
      intro p hp
      obtain ⟨v, hvv, rfl⟩ := List.mem_map.mp hp
      exact zip_support vals scaled hv v hvv)
    (by
      simpa only [List.map_map] using hcertificate)

end SchurFormal
