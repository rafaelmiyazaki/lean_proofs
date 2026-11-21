import Mathlib.LinearAlgebra.Vandermonde
import Mathlib

/-!
# Rigidity of sparse exponential sums

Independent linear-algebra input towards a self-contained
formal proof of the Crittenden--Vanden Eynden covering theorem.

If the bases z_j are pairwise distinct and nonzero, and an
exponential sum F(k) = ∑_j c_j z_j^k vanishes at n consecutive
indices, where n is the number of bases, all coefficients
must vanish. This follows from the Vandermonde determinant.

This module does NOT assert the progression-covering theorem.
-/

namespace SchurFormal

/-- An n-term exponential sum with distinct bases is determined
by its first n values. -/
theorem sparse_exponential_zero_of_initial_zeros
    (n : ℕ) (z coeff : Fin n → ℂ)
    (hz : Function.Injective z)
    (hzero : ∀ i : Fin n,
      (∑ j : Fin n, coeff j * z j ^ (i : ℕ)) = 0) :
    ∀ k : ℕ, (∑ j : Fin n, coeff j * z j ^ k) = 0 := by
  have hcoeff : coeff = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hz hzero
  subst coeff
  simp

/-- If the nonzero bases are distinct, vanishing at any n
consecutive nonnegative indices implies vanishing at every
nonnegative index. -/
theorem sparse_exponential_zero_of_consecutive_zeros
    (n start : ℕ) (z coeff : Fin n → ℂ)
    (hz : Function.Injective z)
    (hnz : ∀ i : Fin n, z i ≠ 0)
    (hzero : ∀ i : Fin n,
      (∑ j : Fin n, coeff j * z j ^ (start + (i : ℕ))) = 0) :
    ∀ k : ℕ, (∑ j : Fin n, coeff j * z j ^ k) = 0 := by
  let shifted : Fin n → ℂ := fun j => coeff j * z j ^ start
  have hshift (i : Fin n) :
      (∑ j : Fin n, shifted j * z j ^ (i : ℕ)) = 0 := by
    simpa only [shifted, pow_add, mul_assoc] using hzero i
  have hcoeffShift : shifted = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hz hshift
  have hcoeff (j : Fin n) : coeff j = 0 := by
    have h := congrFun hcoeffShift j
    change coeff j * z j ^ start = 0 at h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (hnz j))
  have hcoeffAll : coeff = 0 := funext hcoeff
  subst coeff
  simp

/-- Contrapositive: a nonzero exponential sum with n distinct
nonzero bases has at least one nonzero value in every interval
of n consecutive nonnegative integer indices. -/
theorem sparse_exponential_nonzero_in_window
    (n start : ℕ) (z coeff : Fin n → ℂ)
    (hz : Function.Injective z)
    (hnz : ∀ i : Fin n, z i ≠ 0)
    (hNonzero : ∃ k : ℕ,
      (∑ j : Fin n, coeff j * z j ^ k) ≠ 0) :
    ∃ i : Fin n,
      (∑ j : Fin n, coeff j * z j ^ (start + (i : ℕ))) ≠ 0 := by
  by_contra hnone
  have hzeros (i : Fin n) :
      (∑ j : Fin n, coeff j * z j ^ (start + (i : ℕ))) = 0 := by
    by_contra h
    exact hnone ⟨i, h⟩
  obtain ⟨k, hk⟩ := hNonzero
  exact hk (sparse_exponential_zero_of_consecutive_zeros
    n start z coeff hz hnz hzeros k)

end SchurFormal
