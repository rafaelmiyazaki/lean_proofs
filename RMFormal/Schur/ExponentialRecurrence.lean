import Mathlib

/-!
# Sparse exponential sums and their vanishing windows

An independent proof of the linear recurrence principle underlying
the Crittenden--Vanden Eynden covering theorem.

For a list of k pairs (coefficient, base) in C, define
F(n) = ∑ coefficient * base^n.
If F vanishes on k consecutive nonnegative indices, it
vanishes at all later indices. Bases need NOT be distinct,
and need NOT be nonzero; repeated bases are allowed.

The proof is an induction on k, eliminating the first geometric
term with the operator F(n+1)-z*F(n).
No research-specific axioms or hypotheses are introduced.
-/

namespace SchurFormal

def exponentialListSum (xs : List (ℂ × ℂ)) (n : ℕ) : ℂ :=
  (xs.map (fun p => p.1 * p.2 ^ n)).sum

private theorem exponentialListSum_cons
    (p : ℂ × ℂ) (xs : List (ℂ × ℂ)) (n : ℕ) :
    exponentialListSum (p :: xs) n =
      p.1 * p.2 ^ n + exponentialListSum xs n := by
  simp [exponentialListSum]

private theorem exponentialListSum_difference_tail
    (z : ℂ) (xs : List (ℂ × ℂ)) (n : ℕ) :
    exponentialListSum (xs.map (fun p => (p.1 * (p.2 - z), p.2))) n =
      exponentialListSum xs (n + 1) -
        z * exponentialListSum xs n := by
  induction xs with
  | nil =>
    simp [exponentialListSum]
  | cons p ps ih =>
    rw [List.map_cons, exponentialListSum_cons, ih,
      exponentialListSum_cons, exponentialListSum_cons]
    rw [pow_succ]
    ring

private theorem exponentialListSum_elimination
    (p : ℂ × ℂ) (xs : List (ℂ × ℂ)) (n : ℕ) :
    exponentialListSum (p :: xs) (n + 1) -
        p.2 * exponentialListSum (p :: xs) n =
      exponentialListSum
        (xs.map (fun q => (q.1 * (q.2 - p.2), q.2))) n := by
  rw [exponentialListSum_cons, exponentialListSum_cons,
    exponentialListSum_difference_tail]
  rw [pow_succ]
  ring

/-- A k-term exponential sum that is zero at k consecutive
indices is zero at every subsequent index. -/
theorem exponential_list_zero_forward
    (xs : List (ℂ × ℂ)) (start : ℕ)
    (hzeros : ∀ i : ℕ, i < xs.length →
      exponentialListSum xs (start + i) = 0) :
    ∀ n : ℕ, start ≤ n → exponentialListSum xs n = 0 := by
  have aux :
      ∀ k : ℕ, ∀ (ys : List (ℂ × ℂ)) (s : ℕ),
        ys.length = k →
        (∀ i : ℕ, i < k → exponentialListSum ys (s + i) = 0) →
        ∀ n : ℕ, s ≤ n → exponentialListSum ys n = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro ys s hlen hZero n hn
      cases ys with
      | nil =>
        simp [exponentialListSum]
      | cons p tail =>
        let rest : List (ℂ × ℂ) :=
          tail.map (fun q => (q.1 * (q.2 - p.2), q.2))
        have hrestlen : rest.length < k := by
          simp [rest] at *
          omega
        have hzeroRest (i : ℕ) (hi : i < rest.length) :
            exponentialListSum rest (s + i) = 0 := by
          have hi' : i < k := by omega
          have hi'' : i + 1 < k := by
            simp [rest] at hi
            simp at hlen
            omega
          have ha := hZero i hi'
          have hb := hZero (i + 1) hi''
          have hid := exponentialListSum_elimination p tail (s + i)
          change exponentialListSum (p :: tail) (s + i + 1) -
            p.2 * exponentialListSum (p :: tail) (s + i) =
            exponentialListSum rest (s + i) at hid
          have hsucc : s + i + 1 = s + (i + 1) := by omega
          rw [hsucc, hb, ha] at hid
          simpa using hid.symm
        have hrestAll (t : ℕ) (ht : s ≤ t) :
            exponentialListSum rest t = 0 :=
          ih rest.length hrestlen rest s rfl hzeroRest t ht
        have hstep (t : ℕ) (ht : s ≤ t) :
            exponentialListSum (p :: tail) (t + 1) =
              p.2 * exponentialListSum (p :: tail) t := by
          have hid := exponentialListSum_elimination p tail t
          rw [hrestAll t ht] at hid
          exact sub_eq_zero.mp hid
        have hstart : exponentialListSum (p :: tail) s = 0 := by
          simpa using hZero 0 (by simp at hlen; omega)
        have hforward (j : ℕ) :
            exponentialListSum (p :: tail) (s + j) = 0 := by
          induction j with
          | zero => simpa using hstart
          | succ j ihj =>
            calc
              exponentialListSum (p :: tail) (s + (j + 1)) =
                exponentialListSum (p :: tail) ((s + j) + 1) := by
                  congr 1
              _ = p.2 * exponentialListSum (p :: tail) (s + j) :=
                hstep (s + j) (by omega)
              _ = 0 := by rw [ihj]; simp
        have hnEq : n = s + (n - s) := by omega
        rw [hnEq]
        exact hforward (n - s)
  exact aux xs.length xs start rfl hzeros

end SchurFormal
