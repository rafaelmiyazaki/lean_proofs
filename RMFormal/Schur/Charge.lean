import RMFormal.Schur.Definitions

/-! # Arithmetic core of the charge argument (Section 3, Claim 2).
Draft scripts, not yet compiler-verified. -/

namespace SchurFormal

def charge (p q : ℕ) : ℤ := (p : ℤ) - (q : ℤ)

theorem equal_charge_cross_counts
    {p₁ q₁ p₂ q₂ : ℕ}
    (h : charge p₁ q₁ = charge p₂ q₂) :
    p₁ + q₂ = q₁ + p₂ := by
  unfold charge at h
  omega

theorem cross_count_le
    {p₁ q₁ p₂ q₂ m : ℕ}
    (hcharge : charge p₁ q₁ = charge p₂ q₂)
    (h₁ : p₁ + q₁ ≤ m) (h₂ : p₂ + q₂ ≤ m) :
    p₁ + q₂ ≤ m := by
  have hcross := equal_charge_cross_counts hcharge
  omega

end SchurFormal
