import RMFormal.Schur.FiniteSchurRealBound
import RMFormal.Schur.SchurPowerConversion

/-!
# Main quantitative theorem (Theorem 1.1)

Apply the fully formalized weighted local-coloring lemma to
the difference-colored complete graph on Fin N, with
chi=2m+1, ell=m, and q=r. The resulting real bound is
converted to the exact powered natural-number inequality.

This is the MainBoundPowered proposition in Definitions.lean;
no theorem hypothesis is introduced.
-/

namespace SchurFormal

/-- The quantitative generalized Schur Ramsey bound,
in exact natural-number power form. -/
theorem main_bound_powered : MainBoundPowered := by
  intro m r N hm hr color hAvoid
  exact real_schur_bound_to_powered m r N hm
    (finite_schur_bound_real m r N hm hr color hAvoid)

end SchurFormal
