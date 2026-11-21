import RMFormal.Schur.LambertWalk

/-!
# Lambert bounded walks: every partial sum remains in range

This converts the inductive bounded-walk certificate into the
precise prefix-sum inequality used by the pigeonhole step in the
proof of Lambert's minimal zero-sum length theorem.
-/

namespace SchurFormal

/-- Every prefix of a Lambert greedy walk, including the empty
prefix and the full walk, stays inside the interval (-b,a]. -/
theorem LambertBoundedWalk.prefix_bounds
    {α : Type*} {f : α → ℤ} {a b : ℕ}
    {t : ℤ} {order : List α}
    (hwalk : LambertBoundedWalk f a b t order) :
    ∀ j : ℕ, j ≤ order.length →
      -(b : ℤ) < t + ((order.take j).map f).sum ∧
        t + ((order.take j).map f).sum ≤ (a : ℤ) := by
  induction hwalk with
  | nil t hlo hhi =>
      intro j hj
      have hj0 : j = 0 := by simpa using hj
      subst j
      simpa using And.intro hlo hhi
  | cons t i tail hlo hhi hsign hrest ih =>
      intro j hj
      cases j with
      | zero =>
          simpa using And.intro hlo hhi
      | succ j =>
          have hjTail : j ≤ tail.length := by
            simpa using hj
          have hstep := ih j hjTail
          simpa only [List.take_succ_cons, List.map_cons,
            List.sum_cons, add_assoc] using hstep

end SchurFormal
