import RMFormal.Schur.Padding

/-!
# Affine obstruction: integer relations imply generalized Schur solutions

This is the sign-splitting core of Section 4 of
Miyazaki--Mulrenin--Pohoata--Zheng (arXiv:2605.15147).

The remaining gcd/Bezout step will supply the affine relation.
-/

namespace SchurFormal

private theorem int_positive_minus_negative (k : ℤ) :
    ((k.toNat : ℕ) : ℤ) - (((-k).toNat : ℕ) : ℤ) = k := by
  omega

private def repeatWith {ι : Type*} (xs : List ι) (a : ι → ℕ)
    (count : ι → ℕ) : List ℕ :=
  xs.flatMap (fun i => List.replicate (count i) (a i))

private lemma repeatWith_length {ι : Type*} (xs : List ι) (a : ι → ℕ)
    (count : ι → ℕ) :
    (repeatWith xs a count).length = (xs.map count).sum := by
  induction xs with
  | nil => simp [repeatWith]
  | cons i xs ih =>
    simp [repeatWith, ih, Nat.add_comm]

private lemma repeatWith_sum {ι : Type*} (xs : List ι) (a : ι → ℕ)
    (count : ι → ℕ) :
    (repeatWith xs a count).sum =
      (xs.map (fun i => count i * a i)).sum := by
  induction xs with
  | nil => simp [repeatWith]
  | cons i xs ih =>
    simp [repeatWith]
    exact ih

private lemma repeatWith_support {ι : Type*} (xs : List ι)
    (a : ι → ℕ) (count : ι → ℕ) {A : Set ℕ}
    (hA : ∀ i ∈ xs, a i ∈ A) :
    ∀ z ∈ repeatWith xs a count, z ∈ A := by
  induction xs with
  | nil =>
    intro z hz
    simp [repeatWith] at hz
  | cons i xs ih =>
    intro z hz
    change z ∈ (List.replicate (count i) (a i)) ++
      repeatWith xs a count at hz
    rcases List.mem_append.mp hz with h | h
    · have hzi : z = a i := List.eq_of_mem_replicate h
      exact hzi ▸ hA i (by simp)
    · exact ih (fun j hj => hA j (by simp [hj])) z h

private lemma split_coeff_lengths {ι : Type*} (xs : List ι)
    (k : ι → ℤ) :
    (((xs.map (fun i => (k i).toNat)).sum : ℕ) : ℤ) -
      (((xs.map (fun i => (-k i).toNat)).sum : ℕ) : ℤ) =
      (xs.map k).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons, List.sum_cons, Int.natCast_add]
    have hk := int_positive_minus_negative (k i)
    omega

private lemma split_coeff_weights {ι : Type*} (xs : List ι)
    (a : ι → ℕ) (k : ι → ℤ) :
    (((xs.map (fun i => (k i).toNat * a i)).sum : ℕ) : ℤ) -
      (((xs.map (fun i => (-k i).toNat * a i)).sum : ℕ) : ℤ) =
      (xs.map (fun i => k i * (a i : ℤ))).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons, List.sum_cons, Int.natCast_add, Int.natCast_mul]
    have hk := congrArg (fun z : ℤ => z * (a i : ℤ))
      (int_positive_minus_negative (k i))
    nlinarith [ih, hk]

/-- Sign-splitting lemma: any integer relation with
    total coefficient 1 and weighted sum 0 yields a
    nontrivial generalized Schur equation in A.

    This theorem does not assume a residue/gcd characterization;
    it just turns its eventual Bezout certificate into lists of
    terms with correct cardinalities. -/
theorem affine_relation_forces_solution {ι : Type*} {A : Set ℕ}
    (xs : List ι) (a : ι → ℕ) (k : ι → ℤ)
    (hmem : ∀ i ∈ xs, a i ∈ A)
    (hcount : (xs.map k).sum = 1)
    (hweight : (xs.map (fun i => k i * (a i : ℤ))).sum = 0) :
    ∃ m : ℕ, 0 < m ∧ HasEquation A (m + 1) m := by
  let pos := repeatWith xs a (fun i => (k i).toNat)
  let neg := repeatWith xs a (fun i => (-k i).toNat)
  have hlen : (pos.length : ℤ) - (neg.length : ℤ) = 1 := by
    simp only [pos, neg, repeatWith_length]
    rw [split_coeff_lengths]
    exact hcount
  have hsum : (pos.sum : ℤ) - (neg.sum : ℤ) = 0 := by
    simp only [pos, neg, repeatWith_sum]
    rw [split_coeff_weights]
    exact hweight
  have hlen' : pos.length = neg.length + 1 := by omega
  have hsum' : pos.sum = neg.sum := by omega
  have hbase : HasEquation A (neg.length + 1) neg.length := by
    exact ⟨pos, neg, hlen', rfl,
      repeatWith_support xs a (fun i => (k i).toNat) hmem,
      repeatWith_support xs a (fun i => (-k i).toNat) hmem,
      hsum'⟩
  have hpad : HasEquation A
      ((neg.length + 1) * 1 + 1) (neg.length * 1 + 1) :=
    padding_lemma_3_1 (by omega) hbase 1 1
  refine ⟨neg.length + 1, by omega, ?_⟩
  simpa only [Nat.mul_one] using hpad

end SchurFormal
