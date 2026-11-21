import RMFormal.Schur.ExponentialRecurrence

/-!
# Product expansions as sparse exponential sums

A product of r expressions `zᵢ ^ n - cᵢ` expands into an exponential sum
with exactly 2^r terms, counting repetitions. Hence, if the product vanishes
at 2^r consecutive indices, it vanishes at every later index.

This is one independent algebraic ingredient for a formal proof of the
Crittenden--Vanden Eynden covering theorem. No covering assertion is made here.
-/

namespace SchurFormal

/-- Enumerate the coefficient/base pairs in the exponential expansion of
a product of geometric differences. -/
def productExponentialTerms : List (ℂ × ℂ) → List (ℂ × ℂ)
  | [] => [(1, 1)]
  | (z, c) :: xs =>
      (productExponentialTerms xs).map (fun p => (p.1, p.2 * z)) ++
      (productExponentialTerms xs).map (fun p => (-c * p.1, p.2))

private theorem exponentialListSum_append (xs ys : List (ℂ × ℂ)) (n : ℕ) :
    exponentialListSum (xs ++ ys) n =
      exponentialListSum xs n + exponentialListSum ys n := by
  simp [exponentialListSum]

private theorem exponentialListSum_map_mulBase
    (xs : List (ℂ × ℂ)) (z : ℂ) (n : ℕ) :
    exponentialListSum (xs.map (fun p => (p.1, p.2 * z))) n =
      z ^ n * exponentialListSum xs n := by
  induction xs with
  | nil =>
      simp [exponentialListSum]
  | cons p ps ih =>
      change p.1 * (p.2 * z) ^ n +
          exponentialListSum (ps.map (fun q => (q.1, q.2 * z))) n =
        z ^ n * (p.1 * p.2 ^ n + exponentialListSum ps n)
      rw [ih, mul_pow]
      ring

private theorem exponentialListSum_map_mulCoeff
    (xs : List (ℂ × ℂ)) (c : ℂ) (n : ℕ) :
    exponentialListSum (xs.map (fun p => (-c * p.1, p.2))) n =
      -c * exponentialListSum xs n := by
  induction xs with
  | nil =>
      simp [exponentialListSum]
  | cons p ps ih =>
      change (-c * p.1) * p.2 ^ n +
          exponentialListSum (ps.map (fun q => (-c * q.1, q.2))) n =
        -c * (p.1 * p.2 ^ n + exponentialListSum ps n)
      rw [ih]
      ring

theorem productExponentialTerms_length (xs : List (ℂ × ℂ)) :
    (productExponentialTerms xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => simp [productExponentialTerms]
  | cons p ps ih =>
      simp [productExponentialTerms, ih, pow_succ, mul_two]

/-- Exact expansion of the product of geometric differences. -/
theorem exponential_product_expansion (xs : List (ℂ × ℂ)) (n : ℕ) :
    exponentialListSum (productExponentialTerms xs) n =
      (xs.map (fun p => p.1 ^ n - p.2)).prod := by
  induction xs with
  | nil =>
      simp [productExponentialTerms, exponentialListSum]
  | cons p ps ih =>
      calc
        exponentialListSum (productExponentialTerms (p :: ps)) n =
            (p.1 ^ n - p.2) *
              exponentialListSum (productExponentialTerms ps) n := by
                rw [productExponentialTerms, exponentialListSum_append,
                    exponentialListSum_map_mulBase,
                    exponentialListSum_map_mulCoeff]
                ring
        _ = ((p :: ps).map (fun q => q.1 ^ n - q.2)).prod := by
                rw [ih]
                simp

/-- A product of r geometric differences which vanishes at 2^r
consecutive indices vanishes at every later index. The bases may
coincide or be zero. -/
theorem exponential_product_zero_forward
    (xs : List (ℂ × ℂ)) (start : ℕ)
    (hzeros : ∀ i : ℕ, i < 2 ^ xs.length →
      (xs.map (fun p => p.1 ^ (start + i) - p.2)).prod = 0) :
    ∀ n : ℕ, start ≤ n →
      (xs.map (fun p => p.1 ^ n - p.2)).prod = 0 := by
  have hzeros' (i : ℕ) (hi : i < (productExponentialTerms xs).length) :
      exponentialListSum (productExponentialTerms xs) (start + i) = 0 := by
    rw [exponential_product_expansion]
    exact hzeros i (by simpa only [productExponentialTerms_length] using hi)
  intro n hn
  rw [← exponential_product_expansion]
  exact exponential_list_zero_forward (productExponentialTerms xs) start
    hzeros' n hn

end SchurFormal
