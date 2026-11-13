/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.PorousMedium.SelfSimilar
import CAS.ExactTactic

/-!
# Parameterizing the Barenblatt family by its mass

The profile satisfies `F_C(√C y) = C^(1/(m-1)) F_1(y)` (`profile_sqrt_smul`), so a linear change of
variables gives `M(C) = C^(1/(m-1) + n/2) M(1)` (`profileMass_scaling`), where the reference mass
`M(1)` is positive. Inverting this scaling law gives an explicit parameter
`profileParameterForMass n m M` with mass `M` for every `M > 0`
(`profileMass_profileParameterForMass`), and the corresponding Barenblatt solution has mass `M` at
every positive time (`integral_barenblatt_prescribed_mass`). SymLean's `cas` tactic checks the
exponent algebra.

Evans's §4.2.2 leaves the constant `b` in the Barenblatt solution (35) free;
`profileParameterForMass` fixes it by the mass.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.2.2, Example (A scaling invariant solution), (27)-(36),
  pp. 185-186.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PorousMedium

open MeasureTheory

variable {n : ℕ}

/-- The power by which profile mass depends on the positive profile parameter. -/
def massExponent (n : ℕ) (m : ℝ) : ℝ := profileExponent m + (n : ℝ) / 2

/-- The mass exponent is positive for every slow-diffusion exponent and every dimension. -/
theorem massExponent_pos (n : ℕ) {m : ℝ} (hm : 1 < m) : 0 < massExponent n m :=
  add_pos_of_pos_of_nonneg (profileExponent_pos hm) (by positivity)

/-- Dilating the profile by `√C` separates the amplitude parameter from its shape. -/
theorem profile_sqrt_smul (m : ℝ) {C : ℝ} (hC : 0 < C) (y : ℝ^n) :
    profile n m C (Real.sqrt C • y) = C ^ profileExponent m * profile n m 1 y := by
  have hgap : C - profileCoefficient n m * ‖Real.sqrt C • y‖ ^ 2 =
      C * (1 - profileCoefficient n m * ‖y‖ ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg C),
      mul_pow, Real.sq_sqrt hC.le]
    cas
  have hpart (z : ℝ) : (C * z)⁺ = C * z⁺ := by
    simp only [posPart_def, mul_max_of_nonneg _ _ hC.le, mul_zero]
  rw [profile, hgap, hpart, Real.mul_rpow hC.le (posPart_nonneg _)]
  rfl

/-- The positive-parameter profile is a scaled copy of the unit-parameter profile. -/
theorem profile_parameter_scaling (m : ℝ) {C : ℝ} (hC : 0 < C) (x : ℝ^n) :
    profile n m C x =
      C ^ profileExponent m * profile n m 1 ((Real.sqrt C)⁻¹ • x) := by
  simpa only [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hC).ne', one_smul] using
    profile_sqrt_smul m hC ((Real.sqrt C)⁻¹ • x)

/-- The mass scales as `C ^ massExponent n m`, by the profile formula and the dilation
Jacobian. -/
theorem profileMass_scaling (m : ℝ) {C : ℝ} (hC : 0 < C) :
    profileMass n m C = C ^ massExponent n m * profileMass n m 1 := by
  unfold profileMass
  simp_rw [profile_parameter_scaling m hC]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure (ℝ^n)) _ (Real.sqrt_nonneg C),
    finrank_euclideanSpace_fin, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hC.le,
    ← Real.rpow_add hC]
  congr 1
  unfold massExponent
  cas

/-- The explicit profile parameter whose solution has prescribed mass `M`. -/
def profileParameterForMass (n : ℕ) (m M : ℝ) : ℝ :=
  (M / profileMass n m 1) ^ (massExponent n m)⁻¹

/-- A prescribed positive mass produces a strictly positive profile parameter. -/
theorem profileParameterForMass_pos {m M : ℝ} (hm : 1 < m) (hM : 0 < M) :
    0 < profileParameterForMass n m M :=
  Real.rpow_pos_of_pos (div_pos hM (profileMass_pos hm zero_lt_one)) _

/-- The explicit parameter choice gives the prescribed mass. -/
theorem profileMass_profileParameterForMass {m M : ℝ} (hm : 1 < m) (hM : 0 < M) :
    profileMass n m (profileParameterForMass n m M) = M := by
  rw [profileMass_scaling m (profileParameterForMass_pos hm hM), profileParameterForMass]
  have hunit := profileMass_pos (n := n) hm zero_lt_one
  have hpower := massExponent_pos n hm
  have hbase := div_pos hM hunit
  rw [← Real.rpow_mul hbase.le, inv_mul_cancel₀ hpower.ne',
    Real.rpow_one, div_mul_cancel₀ M hunit.ne']

/-- Every positive mass is attained by a positive profile parameter. -/
theorem exists_profileParameter_of_mass {m M : ℝ} (hm : 1 < m) (hM : 0 < M) :
    ∃ C > 0, profileMass n m C = M :=
  ⟨profileParameterForMass n m M, profileParameterForMass_pos hm hM,
    profileMass_profileParameterForMass hm hM⟩

/-- The explicit profile parameter gives the prescribed conserved mass at every positive time. -/
theorem integral_barenblatt_prescribed_mass {m M t : ℝ}
    (hm : 1 < m) (hM : 0 < M) (ht : 0 < t) :
    (∫ x : ℝ^n, barenblatt n m (profileParameterForMass n m M) t x) = M := by
  rw [integral_barenblatt ht, profileMass_profileParameterForMass hm hM]

end PorousMedium
