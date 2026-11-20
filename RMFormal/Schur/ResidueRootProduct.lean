import RMFormal.Schur.ProductExponential
import RMFormal.Schur.ResidueNecessity
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Arithmetic progression coverings via sparse exponential products

For a positive modulus d, a primitive d-th root of unity ζ converts the
condition n % d = a (for 0 ≤ a < d) into ζ^n = ζ^a.

A covering by k residue classes therefore forces a product of k
geometric differences to vanish. The product has at most 2^k
exponential terms, so 2^k consecutive zeros force all subsequent
values to vanish.

This supplies an independent proof of the residue-covering principle
needed for the upper direction of Theorem 1.3, without assuming any
version of the Crittenden--Vanden Eynden theorem.
-/

namespace SchurFormal

private noncomputable def coveringRoot (d : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (d : ℂ))

private theorem coveringRoot_primitive (d : ℕ) (hd : d ≠ 0) :
    IsPrimitiveRoot (coveringRoot d) d := by
  simpa only [coveringRoot] using Complex.isPrimitiveRoot_exp d hd

/-- Translate a residue class into equality of powers of a primitive root. -/
theorem primitive_root_pow_eq_iff_mod
    (ζ : ℂ) (d n a : ℕ) (hd : 0 < d) (ha : a < d)
    (hζ : IsPrimitiveRoot ζ d) :
    (ζ ^ n = ζ ^ a) ↔ n % d = a := by
  have hmod : ζ ^ (n % d) = ζ ^ n := by
    rw [hζ.eq_orderOf]
    exact pow_mod_orderOf ζ n
  constructor
  · intro h
    exact hζ.pow_inj (Nat.mod_lt n hd) ha (hmod.trans h)
  · intro h
    calc
      ζ ^ n = ζ ^ (n % d) := hmod.symm
      _ = ζ ^ a := by rw [h]

private theorem product_zero_of_factor
    (xs : List (ℂ × ℂ)) (n : ℕ) (p : ℂ × ℂ)
    (hp : p ∈ xs) (heq : p.1 ^ n = p.2) :
    (xs.map (fun q => q.1 ^ n - q.2)).prod = 0 := by
  induction xs with
  | nil => simp at hp
  | cons q qs ih =>
      have hp' : p = q ∨ p ∈ qs := by
        simpa only [List.mem_cons] using hp
      simp only [List.map_cons, List.prod_cons]
      rcases hp' with h | h
      · subst p
        simp [heq]
      · rw [ih h]
        simp

private theorem factor_of_product_zero
    (xs : List (ℂ × ℂ)) (n : ℕ)
    (hzero : (xs.map (fun q => q.1 ^ n - q.2)).prod = 0) :
    ∃ p ∈ xs, p.1 ^ n = p.2 := by
  induction xs with
  | nil =>
      simp at hzero
  | cons q qs ih =>
      simp only [List.map_cons, List.prod_cons] at hzero
      rcases mul_eq_zero.mp hzero with hq | hqs
      · exact ⟨q, by simp, sub_eq_zero.mp hq⟩
      · obtain ⟨p, hp, heq⟩ := ih hqs
        exact ⟨p, by simp [hp], heq⟩

/-- The residue-covering consequence of the Crittenden--Vanden Eynden
theorem, proved here from the sparse exponential-product recurrence. -/
theorem residue_covering_from_exponential :
    ResidueCoveringPrinciple := by
  intro k hk d a hparams hcover
  classical
  let ζ : Fin k → ℂ := fun i => coveringRoot (d i)
  let xs : List (ℂ × ℂ) :=
    List.ofFn (fun i : Fin k => (ζ i, ζ i ^ a i))
  have hprim (i : Fin k) : IsPrimitiveRoot (ζ i) (d i) := by
    apply coveringRoot_primitive
    have hi := (hparams i).1
    omega
  have hmem (i : Fin k) : (ζ i, ζ i ^ a i) ∈ xs := by
    change (ζ i, ζ i ^ a i) ∈
      List.ofFn (fun j : Fin k => (ζ j, ζ j ^ a j))
    exact (List.mem_ofFn' _ _).mpr ⟨i, rfl⟩
  have hzero_of_cover (n : ℕ) (hn : 1 ≤ n)
      (hn' : n ≤ 2 ^ k) :
      (xs.map (fun p => p.1 ^ n - p.2)).prod = 0 := by
    obtain ⟨i, hi⟩ := hcover n hn hn'
    apply product_zero_of_factor xs n (ζ i, ζ i ^ a i) (hmem i)
    exact (primitive_root_pow_eq_iff_mod
      (ζ i) (d i) n (a i)
      (by have := (hparams i).1; omega)
      (hparams i).2.2 (hprim i)).mpr hi
  have hzeros (j : ℕ) (hj : j < 2 ^ xs.length) :
      (xs.map (fun p => p.1 ^ (1 + j) - p.2)).prod = 0 := by
    have hlength : xs.length = k := by simp [xs]
    have hj' : 1 + j ≤ 2 ^ k := by
      rw [hlength] at hj
      omega
    exact hzero_of_cover (1 + j) (by omega) hj'
  let N : ℕ := ∏ i : Fin k, d i
  have hNpos : 0 < N := by
    dsimp [N]
    apply Finset.prod_pos
    intro i _
    have hi := (hparams i).1
    omega
  have hdiv (i : Fin k) : d i ∣ N := by
    dsimp [N]
    exact Finset.dvd_prod_of_mem (fun j : Fin k => d j) (Finset.mem_univ i)
  have hzeroN :
      (xs.map (fun p => p.1 ^ N - p.2)).prod = 0 :=
    exponential_product_zero_forward xs 1 hzeros N (by omega)
  obtain ⟨p, hp, heq⟩ := factor_of_product_zero xs N hzeroN
  have hp' : p ∈ List.ofFn (fun i : Fin k => (ζ i, ζ i ^ a i)) := hp
  obtain ⟨i, rfl⟩ :=
    (List.mem_ofFn' (fun i : Fin k => (ζ i, ζ i ^ a i)) p).mp hp'
  change ζ i ^ N = ζ i ^ a i at heq
  have hmod : N % d i = a i :=
    (primitive_root_pow_eq_iff_mod
      (ζ i) (d i) N (a i)
      (by have := (hparams i).1; omega)
      (hparams i).2.2 (hprim i)).mp heq
  refine ⟨i, ?_⟩
  calc
    0 % d i = N % d i := by simp [Nat.mod_eq_zero_of_dvd (hdiv i)]
    _ = a i := hmod

/-- Unconditional general upper bound in Theorem 1.3. -/
theorem two_power_upper_unconditional : TwoPowerUpper :=
  two_power_upper_of_covering residue_covering_from_exponential

end SchurFormal
