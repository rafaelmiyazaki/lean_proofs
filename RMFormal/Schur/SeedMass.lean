import Mathlib

/-!
# Large initial color-neighborhood mass

In the d ≥ 2 case of weighted Lemma 2.1, choose an incident
color with neighbor mass at least 1/d of all neighbors.
Since the central vertex has strictly positive weight,
the closed color-neighborhood carries strictly more than
one d-th of the total vertex mass.

This lemma is the numerical step between weighted incident-color
pigeonholing and the slow-growth layer argument.
-/

namespace SchurFormal

theorem heavy_neighbor_seed_mass
    (d : ℕ) (hd : 2 ≤ d)
    (total base neighbor : ℝ)
    (hbase : 0 < base)
    (hNeighbor : total - base ≤ (d : ℝ) * neighbor) :
    total / (d : ℝ) < base + neighbor := by
  have hdR : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpos : 0 < ((d : ℝ) - 1) * base :=
    mul_pos (by linarith) hbase
  apply (div_lt_iff₀ (by linarith : (0 : ℝ) < (d : ℝ))).mpr
  nlinarith

end SchurFormal
