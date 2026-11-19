import RMFormal.Schur.ResidueNecessity

/-!
# An explicit interface to the Crittenden--Vanden Eynden theorem

The independent Lean formalization of this theorem in
https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos275.lean
uses the same mathematical statement, with a different Lean/Mathlib version.

This module proves that the known theorem statement is exactly the
remaining input for the general upper half of Theorem 1.3.
It does NOT import or assume the third-party proof as an axiom.
-/

namespace SchurFormal

/-- The classical arithmetic-progression covering theorem:
    if r progressions cover 2^r consecutive integers, they cover Z.
    This is a PROPOSITION, NOT A PROVED THEOREM in our repository. -/
def CVECoveringStatement : Prop :=
  ∀ (r : ℕ) (a : Fin r → ℤ) (d : Fin r → ℕ),
    (∃ t : ℤ, ∀ x ∈ Set.Ico t (t + (2 : ℤ) ^ r),
      ∃ i : Fin r, x ≡ a i [ZMOD d i]) →
    ∀ x : ℤ, ∃ i : Fin r, x ≡ a i [ZMOD d i]

/-- The integer covering statement implies the specialized
    residue-covering principle used by the Schur upper bound. -/
theorem residue_covering_of_cve
    (hcve : CVECoveringStatement) : ResidueCoveringPrinciple := by
  intro k _ d a hparams hcover
  have hIco : ∀ x ∈ Set.Ico (1 : ℤ) (1 + (2 : ℤ) ^ k),
      ∃ i : Fin k, x ≡ (a i : ℤ) [ZMOD d i] := by
    intro x hx
    have hnonneg : 0 ≤ x := by
      have hlowZ : (1 : ℤ) ≤ x := hx.1
      omega
    have hxcast : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hnonneg
    have hpow : (((2 ^ k : ℕ) : ℤ)) = (2 : ℤ) ^ k := by norm_cast
    have hlow : 1 ≤ x.toNat := by
      have hcast : (1 : ℤ) ≤ (x.toNat : ℤ) := by
        rw [hxcast]
        exact hx.1
      exact_mod_cast hcast
    have hupp : x.toNat ≤ 2 ^ k := by
      have hcast : (x.toNat : ℤ) ≤ ((2 ^ k : ℕ) : ℤ) := by
        rw [hxcast, hpow]
        have huppZ : x < 1 + (2 : ℤ) ^ k := hx.2
        omega
      exact_mod_cast hcast
    obtain ⟨i, hi⟩ := hcover x.toNat hlow hupp
    refine ⟨i, ?_⟩
    have hnat : x.toNat ≡ a i [MOD d i] := by
      change x.toNat % d i = a i % d i
      simpa [Nat.mod_eq_of_lt (hparams i).2.2] using hi
    have hint : (x.toNat : ℤ) ≡ (a i : ℤ) [ZMOD d i] :=
      Int.natCast_modEq_iff.mpr hnat
    simpa only [hxcast] using hint
  obtain ⟨i, hi⟩ := hcve k (fun i => (a i : ℤ)) d ⟨1, hIco⟩ 0
  refine ⟨i, ?_⟩
  have hnat : (0 : ℕ) ≡ a i [MOD d i] := by
    apply Int.natCast_modEq_iff.mp
    simpa using hi
  change (0 : ℕ) % d i = a i % d i at hnat
  simpa [Nat.mod_eq_of_lt (hparams i).2.2] using hnat

/-- The upper half of Theorem 1.3 is proved assuming only the
    classical covering theorem, whose statement is explicit. -/
theorem two_power_upper_of_cve (hcve : CVECoveringStatement) :
    TwoPowerUpper :=
  two_power_upper_of_covering (residue_covering_of_cve hcve)

end SchurFormal
