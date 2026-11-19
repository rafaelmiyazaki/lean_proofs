import RMFormal.Schur.Definitions

/-!
# Exact two-color threshold

For any 2-coloring of [4], one of the identities
  1+1=2, 2+2=4, 1+3=4, 2+2+2=3+3
is monochromatic. Thus the upper direction of Theorem 1.3 holds at r=2,
independently of the general covering theorem.
-/

namespace SchurFormal

/-- A small finite pigeonhole fact: one of the four useful
monochromatic configurations must occur. -/
private theorem two_color_pattern (a b c d : Fin 2) :
    a = b ∨ b = d ∨ (a = c ∧ a = d) ∨ b = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

/-- Theorem 1.3, upper direction at two colors, without assumptions. -/
theorem two_color_four (color : ℕ → Fin 2) :
    ∃ m : ℕ, 0 < m ∧ MonochromaticSolution 2 4 (m + 1) m color := by
  rcases two_color_pattern (color 1) (color 2) (color 3) (color 4) with
    h12 | h24 | h134 | h23
  · refine ⟨1, by decide, color 1, [1, 1], [2],
      by decide, by decide, ?_, ?_, by decide⟩
    · simp [ColorClass, PositiveInterval]
    · simp [ColorClass, PositiveInterval, h12]
  · refine ⟨1, by decide, color 2, [2, 2], [4],
      by decide, by decide, ?_, ?_, by decide⟩
    · simp [ColorClass, PositiveInterval]
    · simp [ColorClass, PositiveInterval, h24]
  · rcases h134 with ⟨h13, h14⟩
    refine ⟨1, by decide, color 1, [1, 3], [4],
      by decide, by decide, ?_, ?_, by decide⟩
    · simp [ColorClass, PositiveInterval, h13]
    · simp [ColorClass, PositiveInterval, h14]
  · refine ⟨2, by decide, color 2, [2, 2, 2], [3, 3],
      by decide, by decide, ?_, ?_, by decide⟩
    · simp [ColorClass, PositiveInterval]
    · simp [ColorClass, PositiveInterval, h23]

end SchurFormal
