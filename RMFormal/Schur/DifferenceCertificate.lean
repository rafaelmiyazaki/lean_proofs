import RMFormal.Schur.AffineRelation

/-!
# Explicit Bezout difference certificates

This module turns the arithmetic certificate
  1 = sum_i c_i (a_i - b)
into the signed affine relation needed by
`affine_relation_forces_solution`.

The existence of such a certificate (via gcd/Bezout and suitable
normalization) is the remaining substantive step of the full
affine residue characterization.
-/

namespace SchurFormal

private lemma sum_mul_left {ι : Type*} (xs : List ι)
    (f : ι → ℤ) (z : ℤ) :
    (xs.map (fun i => z * f i)).sum = z * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private lemma sum_difference_identity {ι : Type*} (xs : List ι)
    (f : ι → ℕ) (c : ι → ℤ) (b : ℕ) :
    (xs.map (fun i => c i * ((f i : ℤ) - (b : ℤ)))).sum =
      (xs.map (fun i => c i * (f i : ℤ))).sum -
        (b : ℤ) * (xs.map c).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

/-- A Bezout certificate expressing 1 as a combination of differences
    from one chosen base point forces a generalized Schur equation. -/
theorem difference_certificate_forces_solution
    {ι : Type*} {A : Set ℕ}
    (b : ℕ) (hb : b ∈ A)
    (xs : List ι) (a : ι → ℕ) (c : ι → ℤ)
    (hmem : ∀ i ∈ xs, a i ∈ A)
    (hcomb : (xs.map (fun i =>
      c i * ((a i : ℤ) - (b : ℤ)))).sum = 1) :
    ∃ m : ℕ, 0 < m ∧ HasEquation A (m + 1) m := by
  let total : ℤ := (xs.map c).sum
  let pairs : List (ℤ × ℕ) :=
    (1 + (b : ℤ) * total, b) ::
      xs.map (fun i => (-(b : ℤ) * c i, a i))
  have hpairs : ∀ p ∈ pairs, p.2 ∈ A := by
    intro p hp
    rcases List.mem_cons.mp hp with hfirst | hrest
    · have hpb : p.2 = b := congrArg Prod.snd hfirst
      exact hpb.symm ▸ hb
    · obtain ⟨i, hi, heq⟩ := List.mem_map.mp hrest
      have hpa : p.2 = a i := by simpa [heq]
      exact hpa.symm ▸ hmem i hi
  have hcount : (pairs.map Prod.fst).sum = 1 := by
    simp only [pairs, List.map_cons, List.sum_cons, List.map_map]
    change (1 + (b : ℤ) * total) +
      (xs.map (fun i => -(b : ℤ) * c i)).sum = 1
    rw [sum_mul_left xs c (-(b : ℤ))]
    ring
  have hweight :
      (pairs.map (fun p => p.1 * (p.2 : ℤ))).sum = 0 := by
    simp only [pairs, List.map_cons, List.sum_cons, List.map_map]
    change (1 + (b : ℤ) * total) * (b : ℤ) +
      (xs.map (fun i => (-(b : ℤ) * c i) * (a i : ℤ))).sum = 0
    have hmul :
        (xs.map (fun i => (-(b : ℤ) * c i) * (a i : ℤ))).sum =
          -(b : ℤ) * (xs.map (fun i => c i * (a i : ℤ))).sum := by
      calc
        _ = (xs.map (fun i => -(b : ℤ) * (c i * (a i : ℤ)))).sum := by
          congr 1
          ext i
          ring
        _ = -(b : ℤ) * (xs.map (fun i => c i * (a i : ℤ))).sum :=
          sum_mul_left xs (fun i => c i * (a i : ℤ)) (-(b : ℤ))
    rw [hmul]
    have hdiff := sum_difference_identity xs a c b
    dsimp [total]
    nlinarith [hcomb, hdiff]
  exact affine_relation_forces_solution pairs Prod.snd Prod.fst
    hpairs hcount hweight

end SchurFormal
