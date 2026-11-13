/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.PlanarKernelBalls
public import CAS.CEGA
public meta import PDE.Numerics.Certificates.PlanarKernelBalls

/-!
# Certified values of the constants of the sharp Hölder estimates

Ten-digit enclosures, each from one ball check at precision `2 ^ -200` decided by `cega [fast]`,
the certified evaluation tactic of SymLean (our verified computer algebra system); the balls are
built from FloatLib's rational arctangent and logarithm enclosures. The constant `C_{K₂,low}` is
that of Chen and Hou II, Supplementary material II, (5.11), whose closed form (5.12) is
`(log 2 - 2 f_s(1)) / 2`.

## Main results

* `halfPowerIntegral_one_mem`: `0.2437477471 ≤ f_s(1) ≤ 0.2437477472`.
* `integral_Ioi_sq_div_one_add_pow_four_bounds`: `1.1107207345 ≤ ∫₀^∞ s² / (1 + s⁴) ds ≤
  1.1107207346`, that is `f_s(∞) = π / (2√2)`.
* `kernelTwoLow_bounds`: `0.1028258430 ≤ C_{K₂,low} ≤ 0.1028258431`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II, Section 5.1.2, (5.5), (5.11) and (5.12).
  <https://arxiv.org/abs/2305.05660v3>
* R. J. George, W. Adkisson and A. Anandkumar, "FloatLib: Verified Floating-Point Arithmetic in
  Lean", arXiv:2609.19352, 2026.
  <https://arxiv.org/abs/2609.19352>, code: <https://github.com/lean-dojo/FloatLib>
-/

@[expose] public section

namespace PotentialTheory.Planar

open CAS.Numerics CAS.Numerics.PlanarKernel

/-- The ball check behind `halfPowerIntegral_one_mem`. -/
def halfPowerOneCheck : Bool :=
  halfPowerAtOk 200 200 1 && IntervalBalls.checkBoundsCertain 200
    (2437477471 / 10 ^ 10, 2437477472 / 10 ^ 10) (halfPowerAtBall 200 40 200 1)

/-- The ball check enclosing `f_s(1)` in `[0.2437477471, 0.2437477472]` succeeds. -/
theorem halfPowerOneCheck_eq : halfPowerOneCheck = true := by
  cega [fast]

/-- `0.2437477471 ≤ f_s(1) ≤ 0.2437477472`. -/
theorem halfPowerIntegral_one_mem :
    (2437477471 / 10 ^ 10 : ℝ) ≤ halfPowerIntegral 1 ∧
      halfPowerIntegral 1 ≤ (2437477472 / 10 ^ 10 : ℝ) := by
  have h := halfPowerOneCheck_eq
  simp only [halfPowerOneCheck, Bool.and_eq_true] at h
  have := halfPowerIntegral_mem h.1 h.2
  push_cast at this
  exact this

/-- The ball check behind `integral_Ioi_sq_div_one_add_pow_four_bounds`. -/
def halfPowerLimitCheck : Bool :=
  GridBall.posCertain (IntervalBalls.constMul 2 (sqrtTwoBall 200 200)).lo &&
    IntervalBalls.checkBoundsCertain 200 (11107207345 / 10 ^ 10, 11107207346 / 10 ^ 10)
      (halfPowerLimitBall 200 40 200)

/-- The ball check enclosing `∫₀^∞ s² / (1 + s⁴) ds` in `[1.1107207345, 1.1107207346]` succeeds. -/
theorem halfPowerLimitCheck_eq : halfPowerLimitCheck = true := by
  cega [fast]

/-- `1.1107207345 ≤ ∫₀^∞ s² / (1 + s⁴) ds ≤ 1.1107207346`; the integral is `π / (2√2)` by
`integral_Ioi_sq_div_one_add_pow_four`. -/
theorem integral_Ioi_sq_div_one_add_pow_four_bounds :
    (11107207345 / 10 ^ 10 : ℝ) ≤ ∫ s in Set.Ioi (0 : ℝ), s ^ 2 / (1 + s ^ 4) ∧
      ∫ s in Set.Ioi (0 : ℝ), s ^ 2 / (1 + s ^ 4) ≤ (11107207346 / 10 ^ 10 : ℝ) := by
  have h := halfPowerLimitCheck_eq
  simp only [halfPowerLimitCheck, Bool.and_eq_true] at h
  have := integral_Ioi_sq_div_one_add_pow_four_mem h.1 h.2
  push_cast at this
  exact this

/-- The ball check behind `kernelTwoLow_bounds`. -/
def kernelTwoLowCheck : Bool :=
  halfPowerAtOk 200 200 1 && IntervalBalls.checkBoundsCertain 200
    (1028258430 / 10 ^ 10, 1028258431 / 10 ^ 10) (kernelTwoLowBall 200 40 200)

/-- The ball check enclosing `C_{K₂,low}` in `[0.1028258430, 0.1028258431]` succeeds. -/
theorem kernelTwoLowCheck_eq : kernelTwoLowCheck = true := by
  cega [fast]

/-- **`C_{K₂,low} = 0.10282584…`**: `0.1028258430 ≤ ∫₀¹ ∫₀^{y₁²} |K₂(y)| y₂^{1/2} dy₂ dy₁ ≤
0.1028258431`. -/
theorem kernelTwoLow_bounds :
    (1028258430 / 10 ^ 10 : ℝ) ≤
        ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x ^ 2, |hessianKernel 0 0 !₂[x, y]| * √y ∧
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x ^ 2, |hessianKernel 0 0 !₂[x, y]| * √y ≤
        (1028258431 / 10 ^ 10 : ℝ) := by
  have h := kernelTwoLowCheck_eq
  simp only [kernelTwoLowCheck, Bool.and_eq_true] at h
  have := kernelTwoLow_mem h.1 h.2
  push_cast at this
  exact this

end PotentialTheory.Planar
