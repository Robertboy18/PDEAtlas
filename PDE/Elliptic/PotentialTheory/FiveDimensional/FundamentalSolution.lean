/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.FourPlusOne
public import PDE.Elliptic.PotentialTheory.FiveDimensional.RegularizedKernel
public import PDE.Elliptic.PotentialTheory.FundamentalSolution

/-!
# The five-dimensional Newtonian kernel

The Newtonian kernel in five dimensions has the explicit radial formula
`1 / (8π² |X|³)`. It is invariant under orthogonal transformations of the
first four coordinates and is the pointwise limit of its smooth regularizations.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter LineDeriv TopologicalSpace SobolevSpace
open scoped Distributions ENNReal Topology
open PDE.Analysis

namespace PotentialTheory

/-- The five-dimensional fundamental solution is `1 / (8π² |X|³)`,
including the totalized value zero at the pole. -/
theorem fundamentalSolution_five (X : ℝ^5) :
    fundamentalSolution 5 X = (1 / (8 * Real.pi ^ 2)) * ‖X‖ ^ (-3 : ℝ) := by
  by_cases hX : X = 0
  · subst X
    norm_num [PotentialTheory.fundamentalSolution]
  · have hnorm : 0 < ‖X‖ := norm_pos_iff.mpr hX
    have hnegThree : ‖X‖ ^ (-3 : ℝ) = (‖X‖ ^ (3 : ℕ))⁻¹ := by
      simp [Real.rpow_neg (x := ‖X‖) (norm_nonneg X) (3 : ℝ)]
    rw [fundamentalSolution_of_three_le (by norm_num : 3 ≤ 5),
      PDE.Analysis.unitBallVolume_five, hnegThree]
    norm_num
    field_simp [Real.pi_ne_zero, hnorm.ne']

/-- `Γ₅` depends only on `‖X‖`, so it is invariant under any orthogonal
transformation of the first four coordinates.
-/
@[simp]
theorem fundamentalSolution_five_firstFourLinearIsometryEquiv
    (e : ℝ^4 ≃ₗᵢ[ℝ] ℝ^4)
    (X : ℝ^5) :
    (fundamentalSolution 5) (firstFourLinearIsometryEquiv e X) =
      (fundamentalSolution 5) X := by
  exact PotentialTheory.fundamentalSolution_eq_of_norm_eq
    ((firstFourLinearIsometryEquiv e).norm_map X)

/-- Away from the pole, the smooth regularization converges pointwise to the
five-dimensional Newtonian kernel.
-/
theorem fiveDimensionalGammaRegularized_tendsto
    (X : ℝ^5) (hX : X ≠ 0) :
    Tendsto (fun ε : ℝ ↦ fiveDimensionalGammaRegularized ε X)
      (nhds 0) (nhds ((fundamentalSolution 5) X)) := by
  have hsquare : Tendsto (fun ε : ℝ ↦ ε ^ 2) (nhds 0) (nhds (0 ^ 2)) :=
    tendsto_id.pow 2
  have hbase : Tendsto (fun ε : ℝ ↦ ‖X‖ ^ 2 + ε ^ 2)
      (nhds 0) (nhds (‖X‖ ^ 2 + 0 ^ 2)) := tendsto_const_nhds.add hsquare
  have hnormsq : ‖X‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hX)
  have hpow := hbase.rpow_const (p := (-(3 / 2 : ℝ))) (Or.inl (by simpa using hnormsq))
  have hnormPower : (‖X‖ ^ 2) ^ (-(3 / 2 : ℝ)) = ‖X‖ ^ (-3 : ℝ) := by
    rw [← Real.rpow_natCast_mul (norm_nonneg X) 2 (-(3 / 2 : ℝ))]
    congr 1
    ring
  simpa [fiveDimensionalGammaRegularized, fundamentalSolution_five, hnormPower] using
    tendsto_const_nhds.mul hpow

end PotentialTheory
