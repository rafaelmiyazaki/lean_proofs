import RMFormal.Schur.DifferenceCertificate

/-!
# Finite Bezout certificates for lists of integers

We build, by induction, a coefficient list witnessing the gcd
of an arbitrary integer list. The two-variable Bezout identity
is provided by Mathlib's `Int.gcd_eq_gcd_ab`.

The result will later be instantiated on differences `a_i - b`.
-/

namespace SchurFormal

/-- The positive gcd of the entries of a finite integer list
    (zero for an empty list). -/
def integerListGcd : List ℤ → ℕ
  | [] => 0
  | x :: xs => Int.gcd x (integerListGcd xs : ℤ)

private lemma zipWith_scale_right (xs cs : List ℤ) (b : ℤ) :
    (List.zipWith (fun x c => x * (b * c)) xs cs).sum =
      b * (List.zipWith (fun x c => x * c) xs cs).sum := by
  induction xs generalizing cs with
  | nil => simp
  | cons x xs ih =>
    cases cs with
    | nil => simp
    | cons c cs =>
      simp only [List.zipWith, List.sum_cons]
      rw [ih cs]
      ring

private lemma zipWith_mul_map_right (xs cs : List ℤ) (b : ℤ) :
    (List.zipWith (fun x c => x * c) xs
      (cs.map (fun c => b * c))).sum =
      (List.zipWith (fun x c => x * (b * c)) xs cs).sum := by
  induction xs generalizing cs with
  | nil => simp
  | cons x xs ih =>
    cases cs with
    | nil => simp
    | cons c cs =>
      simp only [List.map_cons, List.zipWith, List.sum_cons]
      rw [ih cs]

/-- Finite-list Bezout identity, with explicit coefficient list.
    The coefficient list has the same length as the input list. -/
theorem integerListGcd_bezout (xs : List ℤ) :
    ∃ cs : List ℤ, cs.length = xs.length ∧
      (List.zipWith (fun x c => x * c) xs cs).sum =
        (integerListGcd xs : ℤ) := by
  induction xs with
  | nil =>
    exact ⟨[], rfl, by simp [integerListGcd]⟩
  | cons x xs ih =>
    obtain ⟨cs, hlen, hbez⟩ := ih
    let g : ℤ := (integerListGcd xs : ℤ)
    let u : ℤ := Int.gcdA x g
    let v : ℤ := Int.gcdB x g
    refine ⟨u :: cs.map (fun c => v * c), by simpa [hlen], ?_⟩
    have hscale :
        (List.zipWith (fun x c => x * c) xs
          (cs.map (fun c => v * c))).sum =
          v * (List.zipWith (fun x c => x * c) xs cs).sum :=
      (zipWith_mul_map_right xs cs v).trans
        (zipWith_scale_right xs cs v)
    simp only [List.zipWith, List.sum_cons]
    rw [hscale, hbez]
    change x * u + v * g = (Int.gcd x g : ℤ)
    calc
      x * u + v * g = x * u + g * v := by ring
      _ = (Int.gcd x g : ℤ) :=
        (Int.gcd_eq_gcd_ab x g).symm

end SchurFormal
