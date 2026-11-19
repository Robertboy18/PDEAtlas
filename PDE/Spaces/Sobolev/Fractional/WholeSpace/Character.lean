/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import PDE.Common.Euclidean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Temperate growth of the Fourier character

For a real normed space `E` and a continuous real-linear map `L : E →L[ℝ] ℂ` with purely
imaginary values, `x ↦ exp (L x)` has temperate growth. The proof composes Mathlib's
`Complex.hasTemperateGrowth_exp_mul_I` with the imaginary part of `L`. In particular the
character `ξ ↦ exp (2πi⟪h, ξ⟫)` on `ℝ^n` has temperate growth, and so do `ξ ↦ 𝐞 ⟪h, ξ⟫` and
the conjugate character `ξ ↦ 𝐞 (-⟪h, ξ⟫)` that occurs in `VectorFourier.fourierIntegral`.
Temperate growth is the condition under which a function multiplies tempered distributions.

The file also proves `‖exp (2πi t) - 1‖ ≤ min 2 (2π|t|)` and, at `t = ⟪h, ξ⟫`, the bound
`min 2 (2π ‖h‖ ‖ξ‖)`. The exact value `‖exp (i x) - 1‖ = ‖2 sin (x / 2)‖` is Mathlib's
`Complex.norm_exp_I_mul_ofReal_sub_one`.
-/

@[expose] public section

noncomputable section

open scoped Real FourierTransform RealInnerProductSpace

namespace SobolevSpace.Fractional

section TemperateGrowth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exponential of a continuous real-linear map `L : E →L[ℝ] ℂ` with purely imaginary
values has temperate growth. -/
theorem hasTemperateGrowth_cexp_comp (L : E →L[ℝ] ℂ) (hL : ∀ x, (L x).re = 0) :
    Function.HasTemperateGrowth (fun x ↦ Complex.exp (L x)) := by
  have h : (fun x ↦ Complex.exp (L x)) =
      (fun t : ℝ ↦ Complex.exp (t * Complex.I)) ∘ (Complex.imCLM.comp L) := by
    funext x
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, Complex.imCLM_apply]
    congr 1
    apply Complex.ext <;> simp [hL x]
  rw [h]
  exact Complex.hasTemperateGrowth_exp_mul_I.comp (Complex.imCLM.comp L).hasTemperateGrowth

end TemperateGrowth

section Character

variable {n : ℕ}

/-- The real-linear map `ξ ↦ 2πi⟪h, ξ⟫` on `ℝ^n`, whose exponential is the Fourier character
of the shift by `h`. -/
def charSymbolCLM (h : ℝ^n) : ℝ^n →L[ℝ] ℂ :=
  (2 * (π : ℂ) * Complex.I) • (Complex.ofRealCLM.comp (innerSL ℝ h))

/-- `charSymbolCLM h ξ = 2πi⟪h, ξ⟫`. -/
@[simp]
theorem charSymbolCLM_apply (h ξ : ℝ^n) :
    charSymbolCLM h ξ = 2 * π * Complex.I * (⟪h, ξ⟫ : ℝ) := by
  simp [charSymbolCLM]

/-- `charSymbolCLM h` takes purely imaginary values. -/
theorem charSymbolCLM_re (h ξ : ℝ^n) : (charSymbolCLM h ξ).re = 0 := by
  simp [charSymbolCLM_apply, Complex.mul_re, Complex.mul_im]

/-- For every `h ∈ ℝ^n`, the character `ξ ↦ exp (2πi⟪h, ξ⟫)` has temperate growth. -/
theorem hasTemperateGrowth_char (h : ℝ^n) :
    Function.HasTemperateGrowth
      (fun ξ : ℝ^n ↦ Complex.exp (2 * π * Complex.I * (⟪h, ξ⟫ : ℝ))) := by
  simpa using hasTemperateGrowth_cexp_comp (charSymbolCLM h) (charSymbolCLM_re h)

/-- For every `h ∈ ℝ^n`, the character `ξ ↦ 𝐞 ⟪h, ξ⟫` has temperate growth. -/
theorem hasTemperateGrowth_fourierChar_inner (h : ℝ^n) :
    Function.HasTemperateGrowth (fun ξ : ℝ^n ↦ ((𝐞 (⟪h, ξ⟫) : Circle) : ℂ)) := by
  have : (fun ξ : ℝ^n ↦ ((𝐞 (⟪h, ξ⟫) : Circle) : ℂ)) =
      fun ξ : ℝ^n ↦ Complex.exp (2 * π * Complex.I * (⟪h, ξ⟫ : ℝ)) := by
    funext ξ
    rw [Real.fourierChar_apply]
    push_cast
    ring_nf
  rw [this]
  exact hasTemperateGrowth_char h

/-- For every `h ∈ ℝ^n`, the character `ξ ↦ 𝐞 (-⟪h, ξ⟫)` has temperate growth. -/
theorem hasTemperateGrowth_fourierChar_inner_neg (h : ℝ^n) :
    Function.HasTemperateGrowth (fun ξ : ℝ^n ↦ ((𝐞 (-⟪h, ξ⟫) : Circle) : ℂ)) := by
  have : (fun ξ : ℝ^n ↦ ((𝐞 (-⟪h, ξ⟫) : Circle) : ℂ)) =
      fun ξ : ℝ^n ↦ ((𝐞 (⟪-h, ξ⟫) : Circle) : ℂ) := by
    funext ξ
    rw [inner_neg_left]
  rw [this]
  exact hasTemperateGrowth_fourierChar_inner (-h)

end Character

section PointwiseBound

/-- For real `t`, `‖exp (2πi t) - 1‖ ≤ min 2 (2π|t|)`. -/
theorem norm_char_sub_one_le (t : ℝ) :
    ‖Complex.exp (2 * π * Complex.I * t) - 1‖ ≤ min 2 (2 * π * |t|) := by
  have hrw : 2 * (π : ℂ) * Complex.I * t = Complex.I * ((2 * π * t : ℝ) : ℂ) := by
    push_cast
    ring
  refine le_min ?_ ?_
  · have h1 : ‖Complex.exp (2 * (π : ℂ) * Complex.I * t)‖ = 1 := by
      rw [hrw]
      simp [Complex.norm_exp]
    calc ‖Complex.exp (2 * (π : ℂ) * Complex.I * t) - 1‖
        ≤ ‖Complex.exp (2 * (π : ℂ) * Complex.I * t)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [h1]
        norm_num
  · rw [hrw]
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]

/-- For real `t`, `‖𝐞 t - 1‖ ≤ min 2 (2π|t|)`. -/
theorem norm_fourierChar_sub_one_le (t : ℝ) :
    ‖((𝐞 t : Circle) : ℂ) - 1‖ ≤ min 2 (2 * π * |t|) := by
  have hrw : ((𝐞 t : Circle) : ℂ) = Complex.exp (2 * π * Complex.I * t) := by
    rw [Real.fourierChar_apply]
    push_cast
    ring_nf
  rw [hrw]
  exact norm_char_sub_one_le t

/-- For `h ξ ∈ ℝ^n`, `‖exp (2πi⟪h, ξ⟫) - 1‖ ≤ min 2 (2π ‖h‖ ‖ξ‖)`. -/
theorem norm_char_inner_sub_one_le {n : ℕ} (h ξ : ℝ^n) :
    ‖Complex.exp (2 * π * Complex.I * (⟪h, ξ⟫ : ℝ)) - 1‖ ≤
      min 2 (2 * π * (‖h‖ * ‖ξ‖)) := by
  refine (norm_char_sub_one_le _).trans
    (le_min (min_le_left _ _) ((min_le_right _ _).trans ?_))
  exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm h ξ) (by positivity)

end PointwiseBound

end SobolevSpace.Fractional
