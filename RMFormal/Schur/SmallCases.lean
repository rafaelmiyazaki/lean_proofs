import RMFormal.Schur.Definitions

/-!
# One-color small case
Proof draft pending compiler verification.
-/

namespace SchurFormal

theorem one_color_two (color : ℕ → Fin 1) :
    MonochromaticSolution 1 2 2 1 color := by
  refine ⟨0, [1, 1], [2], by decide, by decide, ?_, ?_, by decide⟩
  · intro x hx
    have hx1 : x = 1 := by simpa using hx
    subst x
    exact ⟨⟨by decide, by decide⟩, Subsingleton.elim (color 1) 0⟩
  · intro y hy
    have hy2 : y = 2 := by simpa using hy
    subst y
    exact ⟨⟨by decide, by decide⟩, Subsingleton.elim (color 2) 0⟩

end SchurFormal
