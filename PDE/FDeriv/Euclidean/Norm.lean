/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Fréchet derivative of the Euclidean norm

On a real inner product space the norm is differentiable away from the origin, with
derivative `innerSL ℝ (‖x‖⁻¹ • x)`, the functional `h ↦ ⟪x / ‖x‖, h⟫`.
-/

@[expose] public section

namespace EuclideanNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Away from the origin, the norm has derivative
`h ↦ ⟨‖x‖⁻¹ x, h⟩ℝ`. -/
theorem hasFDerivAt_norm_of_ne_zero {x : E} (hx : x ≠ 0) :
    HasFDerivAt norm (innerSL ℝ ((‖x‖)⁻¹ • x)) x := by
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hxnormSq : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 hxnorm
  have hnormSq : HasFDerivAt (fun y : E ↦ ‖y‖ ^ 2)
      ((2 : ℝ) • innerSL ℝ x) x := by
    convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt using 1
    simpa using (Nat.cast_smul_eq_nsmul ℝ 2 (innerSL ℝ x))
  have hsqrt : HasFDerivAt (fun y : E ↦ √(‖y‖ ^ 2))
      ((1 / (2 * √(‖x‖ ^ 2))) • ((2 : ℝ) • innerSL ℝ x)) x :=
    hnormSq.sqrt hxnormSq
  have hmap : (1 / (2 * √(‖x‖ ^ 2))) • ((2 : ℝ) • innerSL ℝ x) =
      innerSL ℝ ((‖x‖)⁻¹ • x) := by
    calc
      (1 / (2 * √(‖x‖ ^ 2))) • ((2 : ℝ) • innerSL ℝ x) =
          (1 / (2 * ‖x‖)) • ((2 : ℝ) • innerSL ℝ x) := by
        simp [Real.sqrt_sq (norm_nonneg x)]
      _ = ((1 / (2 * ‖x‖)) * 2) • innerSL ℝ x := by
        simp [smul_smul]
      _ = (1 / ‖x‖) • innerSL ℝ x := by
        congr 1
        field_simp [hxnorm]
      _ = innerSL ℝ ((‖x‖)⁻¹ • x) := by
        ext y
        simp [div_eq_inv_mul, mul_comm]
  simpa [pow_two] using hsqrt.congr_fderiv hmap

/-- Away from the origin, `fderiv ℝ norm x = innerSL ℝ (‖x‖⁻¹ • x)`. -/
theorem fderiv_norm_of_ne_zero {x : E} (hx : x ≠ 0) :
    fderiv ℝ norm x = innerSL ℝ ((‖x‖)⁻¹ • x) :=
  (hasFDerivAt_norm_of_ne_zero hx).fderiv

end EuclideanNorm
