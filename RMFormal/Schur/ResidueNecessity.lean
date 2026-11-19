import RMFormal.Schur.ArbitraryGcd
import RMFormal.Schur.TwoPower

/-!
# Necessary affine-residue obstruction

A finite set of positive integers that contains no generalized Schur
solution of any length is contained in a single *nonzero* residue class.
This discharges `ResidueObstructionPrinciple` from `TwoPower.lean`.

The nontrivial ingredient is the already verified arbitrary-gcd
certificate theorem `gcd_differences_dvd_base_forces_solution`.
-/

namespace SchurFormal

/-- List gcd divides the image of each member; proved directly to avoid
    any ambiguity between list maps and integer-cast coercions. -/
private theorem gcd_map_dvd {ι : Type*} (xs : List ι)
    (f : ι → ℤ) (x : ι) (hx : x ∈ xs) :
    (integerListGcd (xs.map f) : ℤ) ∣ f x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst x
      simpa [integerListGcd] using
        (Int.gcd_dvd_left (f y) (integerListGcd (ys.map f) : ℤ))
    · exact dvd_trans
        (by simpa [integerListGcd] using
          (Int.gcd_dvd_right (f y) (integerListGcd (ys.map f) : ℤ)))
        (ih h)

/-- Any set represented by a finite list, with a positive base point,
    either has a generalized Schur solution or lies in a nonzero
    residue class. This is the avoidance form. -/
theorem finite_list_residue_obstruction
    {A : Set ℕ} (b : ℕ) (hb : b ∈ A) (hbpos : 0 < b)
    (vals : List ℕ)
    (hv : ∀ x ∈ vals, x ∈ A)
    (hcover : ∀ x ∈ A, x ∈ vals)
    (hAvoid : ∀ m : ℕ, 0 < m → ¬ HasEquation A (m + 1) m) :
    ∃ d a : ℕ, 2 ≤ d ∧ 0 < a ∧ a < d ∧
      ∀ x ∈ A, x % d = a := by
  let d : ℕ := integerListGcd
    (vals.map (fun x => (x : ℤ) - (b : ℤ)))
  have hnotdvd : ¬ (d : ℤ) ∣ (b : ℤ) := by
    intro hdiv
    obtain ⟨m, hm, hs⟩ :=
      gcd_differences_dvd_base_forces_solution b hb vals hv
        (by simpa only [d] using hdiv)
    exact hAvoid m hm hs
  have hdiff (x : ℕ) (hx : x ∈ A) :
      (d : ℤ) ∣ (x : ℤ) - (b : ℤ) := by
    have hcast : (x : ℤ) ∈ (vals : List ℤ) := by
      simpa using (List.mem_map_of_mem
        (f := fun z : ℕ => (z : ℤ)) (hcover x hx))
    simpa only [d] using
      (gcd_map_dvd (vals : List ℤ)
        (fun z : ℤ => z - (b : ℤ))
        (x : ℤ) hcast)
  by_cases hd0 : d = 0
  · have hsame (x : ℕ) (hx : x ∈ A) : x = b := by
      have h : (0 : ℤ) ∣ (x : ℤ) - (b : ℤ) := by
        simpa only [hd0] using hdiff x hx
      rcases h with ⟨z, hz⟩
      have heq : (x : ℤ) - (b : ℤ) = 0 := by
        simpa using hz
      omega
    refine ⟨b + 1, b, by omega, hbpos, by omega, ?_⟩
    intro x hx
    have hxb := hsame x hx
    simp [hxb, Nat.mod_eq_of_lt (by omega : b < b + 1)]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hdone : d ≠ 1 := by
      intro h1
      apply hnotdvd
      simp [h1]
    have hd2 : 2 ≤ d := by omega
    have hbmod : b % d ≠ 0 := by
      intro hzero
      have hdiv : d ∣ b := Nat.dvd_of_mod_eq_zero hzero
      exact hnotdvd (by exact_mod_cast hdiv)
    refine ⟨d, b % d, hd2, Nat.pos_of_ne_zero hbmod,
      Nat.mod_lt b hdpos, ?_⟩
    intro x hx
    have hbx : (d : ℤ) ∣ (b : ℤ) - (x : ℤ) := by
      simpa only [neg_sub] using (dvd_neg.mpr (hdiff x hx))
    exact (Nat.modEq_iff_dvd.mpr hbx)

/-- The full affine-residue obstruction principle used in
    the upper-half reduction for Theorem 1.3. -/
theorem residue_obstruction_principle :
    ResidueObstructionPrinciple := by
  intro N A hbound hAvoid
  classical
  by_cases hnonempty : ∃ b : ℕ, b ∈ A
  · obtain ⟨b, hb⟩ := hnonempty
    have hbpos : 0 < b := (hbound b hb).1
    let vals : List ℕ :=
      ((Finset.Icc 1 N).filter (fun x => x ∈ A)).toList
    have hv : ∀ x ∈ vals, x ∈ A := by
      intro x hx
      have hx' : x ∈ (Finset.Icc 1 N).filter (fun x => x ∈ A) := by
        exact Finset.mem_toList.mp hx
      exact (Finset.mem_filter.mp hx').2
    have hall : ∀ x ∈ A, x ∈ vals := by
      intro x hx
      apply Finset.mem_toList.mpr
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr (hbound x hx), hx⟩
    exact finite_list_residue_obstruction b hb hbpos vals hv hall hAvoid
  · refine ⟨2, 1, by decide, by decide, by decide, ?_⟩
    intro x hx
    exact False.elim (hnonempty ⟨x, hx⟩)

/-- Theorem 1.3 upper direction is now conditional *only*
    on the Crittenden--Vanden Eynden covering principle. -/
theorem two_power_upper_of_covering
    (hcover : ResidueCoveringPrinciple) :
    TwoPowerUpper :=
  two_power_upper_of_principles residue_obstruction_principle hcover

end SchurFormal
