/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The essential norm of a bounded operator

The essential norm `‖T‖_ess` of a bounded operator `T` on a normed space is its distance to the
compact operators, the norm of `T` in the Calkin algebra. It does not change when a compact
operator is added, it is at most `‖T - K‖` for every compact `K`, and `‖T‖_ess < r` exactly when
`T = T₀ + K` with `K` compact and `‖T₀‖ < r`. This last form is the hypothesis of the theorems
on compact perturbations (`finite_spectrum_norm_ge_of_pow_bound`), and the essential growth
bound of a semigroup (`StronglyContinuousSemigroup.IsComplexLinear.essGrowthBound`) is defined
with it. The submultiplicativity `‖S T‖_ess ≤ ‖S‖_ess ‖T‖_ess` and the essential spectral radius
are not proved here: the spectral decomposition of a semigroup uses one time only and does not
need them.

## Main results

* `essNorm`: the distance from `T` to the compact operators.
* `essNorm_le_norm_sub`, `essNorm_le_norm`: `‖T‖_ess ≤ ‖T - K‖` for every compact `K`, and
  `‖T‖_ess ≤ ‖T‖`.
* `essNorm_lt_iff`: `‖T‖_ess < r` exactly when `‖T - K‖ < r` for some compact `K`.
* `essNorm_add_of_isCompactOperator`, `essNorm_eq_of_isCompactOperator_sub`,
  `essNorm_eq_zero_of_isCompactOperator`: adding a compact operator does not change the
  essential norm, and a compact operator has essential norm `0`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Spectral

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {T K : X →L[𝕜] X}

/-- The essential norm of a bounded operator: its distance to the compact operators. -/
def essNorm (T : X →L[𝕜] X) : ℝ :=
  Metric.infDist T {K : X →L[𝕜] X | IsCompactOperator K}

/-- The essential norm is nonnegative. -/
theorem essNorm_nonneg (T : X →L[𝕜] X) : 0 ≤ essNorm T :=
  Metric.infDist_nonneg

/-- The essential norm of `T` is at most `‖T - K‖` for every compact `K`. -/
theorem essNorm_le_norm_sub (T : X →L[𝕜] X) (hK : IsCompactOperator K) :
    essNorm T ≤ ‖T - K‖ := by
  rw [← dist_eq_norm]
  exact Metric.infDist_le_dist_of_mem hK

/-- The essential norm is at most the norm. -/
theorem essNorm_le_norm (T : X →L[𝕜] X) : essNorm T ≤ ‖T‖ := by
  simpa using essNorm_le_norm_sub T (K := 0) isCompactOperator_zero

/-- `‖T‖_ess < r` exactly when `T` is within `r` of a compact operator. -/
theorem essNorm_lt_iff {r : ℝ} :
    essNorm T < r ↔ ∃ K : X →L[𝕜] X, IsCompactOperator K ∧ ‖T - K‖ < r := by
  rw [essNorm, Metric.infDist_lt_iff ⟨0, isCompactOperator_zero⟩]
  simp only [Set.mem_ofPred_eq, dist_eq_norm]

/-- The essential norm of a compact operator is `0`. -/
theorem essNorm_eq_zero_of_isCompactOperator (hT : IsCompactOperator T) : essNorm T = 0 :=
  le_antisymm (by simpa using essNorm_le_norm_sub T hT) (essNorm_nonneg T)

/-- Adding a compact operator does not increase the essential norm. -/
theorem essNorm_add_le_of_isCompactOperator (T : X →L[𝕜] X) (hK : IsCompactOperator K) :
    essNorm (T + K) ≤ essNorm T := by
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨K', hK', h⟩ := essNorm_lt_iff.mp (lt_add_of_pos_right (essNorm T) hε)
  refine (essNorm_le_norm_sub (T + K) (K := K' + K) (hK'.add hK)).trans_lt ?_
  rwa [add_sub_add_right_eq_sub]

/-- **The essential norm does not see compact operators**: `‖T + K‖_ess = ‖T‖_ess` for compact
`K`. -/
theorem essNorm_add_of_isCompactOperator (T : X →L[𝕜] X) (hK : IsCompactOperator K) :
    essNorm (T + K) = essNorm T := by
  refine le_antisymm (essNorm_add_le_of_isCompactOperator T hK) ?_
  simpa using essNorm_add_le_of_isCompactOperator (T + K) (K := -K) hK.neg

/-- Two operators with a compact difference have the same essential norm. -/
theorem essNorm_eq_of_isCompactOperator_sub {S : X →L[𝕜] X} (h : IsCompactOperator (T - S)) :
    essNorm T = essNorm S := by
  rw [← essNorm_add_of_isCompactOperator S h, add_sub_cancel]

end PDE.Analysis.Spectral
