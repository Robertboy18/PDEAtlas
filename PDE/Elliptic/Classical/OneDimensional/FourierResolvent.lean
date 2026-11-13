/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.SchwartzDifferentialOperators

/-!
# One-dimensional shifted elliptic Fourier resolvent

The shifted elliptic equation `(-∂ₓₓ + λ)u = f` has a pointwise transform-domain solution
formula and quantitative multiplier bound for positive `λ`. The statements are on the
Fourier side.
-/

@[expose] public section

namespace PDE.Elliptic.Classical.OneDimensional.Fourier

open PDE.Analysis.Fourier
open scoped SchwartzMap

/-- The Fourier symbol of the shifted one-dimensional operator `-∂ₓₓ + λ`. -/
noncomputable def shiftedEllipticSymbol1D (lam ξ : ℝ) : ℂ :=
  fourierEllipticSymbol1D ξ + (lam : ℂ)

/-- The complete shifted elliptic operator `-∂ₓₓ + λ` is diagonalized by its shifted elliptic
symbol. Positivity is needed only when the symbol is divided out. -/
theorem fourier_shifted_negative_second_derivative_multiplier (f : 𝓢(ℝ, ℂ))
    (lam x : ℝ) :
    SchwartzMap.fourierTransformCLM ℂ
        (-(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)) +
          (lam : ℂ) • f) x =
      shiftedEllipticSymbol1D lam x *
        SchwartzMap.fourierTransformCLM ℂ f x := by
  calc
    SchwartzMap.fourierTransformCLM ℂ
        (-(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)) +
          (lam : ℂ) • f) x =
        SchwartzMap.fourierTransformCLM ℂ
            (-(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f))) x +
          (lam : ℂ) * SchwartzMap.fourierTransformCLM ℂ f x := by
      simp
    _ = fourierEllipticSymbol1D x * SchwartzMap.fourierTransformCLM ℂ f x +
          (lam : ℂ) * SchwartzMap.fourierTransformCLM ℂ f x := by
      rw [fourier_negative_second_derivative_multiplier]
    _ = shiftedEllipticSymbol1D lam x *
          SchwartzMap.fourierTransformCLM ℂ f x := by
      simp only [shiftedEllipticSymbol1D]
      ring

/-- The shifted elliptic Fourier symbol is the real number `(2πξ)^2 + λ`, embedded in `ℂ`. -/
theorem shiftedEllipticSymbol1D_eq_ofReal (lam ξ : ℝ) :
    shiftedEllipticSymbol1D lam ξ = (((2 * Real.pi * ξ) ^ 2 + lam : ℝ) : ℂ) := by
  simp [shiftedEllipticSymbol1D, fourierEllipticSymbol1D]

/-- For `λ > 0`, the shifted elliptic Fourier symbol never vanishes. -/
theorem shiftedEllipticSymbol1D_ne_zero_of_pos {lam ξ : ℝ} (hpos : 0 < lam) :
    shiftedEllipticSymbol1D lam ξ ≠ 0 := by
  rw [shiftedEllipticSymbol1D_eq_ofReal]
  exact Complex.ofReal_ne_zero.2 (ne_of_gt (by nlinarith [sq_nonneg (2 * Real.pi * ξ)]))

/-- After Fourier transform, division by the shifted symbol solves the scalar algebraic
equation associated with `(-∂ₓₓ + λ)u = f`. -/
theorem shiftedEllipticSymbol1D_mul_div {lam ξ : ℝ} (rhs : ℂ)
    (hpos : 0 < lam) :
    shiftedEllipticSymbol1D lam ξ *
        (rhs / shiftedEllipticSymbol1D lam ξ) = rhs := by
  exact mul_div_cancel₀ rhs
    (shiftedEllipticSymbol1D_ne_zero_of_pos (lam := lam) (ξ := ξ) hpos)

/-- A positive shift gives the pointwise lower symbol bound
`λ ≤ |(2πξ)² + λ|`. -/
theorem shiftedEllipticSymbol1D_le_norm {lam ξ : ℝ} (hpos : 0 < lam) :
    lam ≤ ‖shiftedEllipticSymbol1D lam ξ‖ := by
  rw [shiftedEllipticSymbol1D_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (by nlinarith [sq_nonneg (2 * Real.pi * ξ)])]
  exact le_add_of_nonneg_left (sq_nonneg (2 * Real.pi * ξ))

/-- Quantitative frequencywise resolvent estimate for `-∂ₓₓ + λ`, valid when `λ > 0`. -/
theorem norm_div_shiftedEllipticSymbol1D_le {lam ξ : ℝ} (rhs : ℂ) (hpos : 0 < lam) :
    ‖rhs / shiftedEllipticSymbol1D lam ξ‖ ≤ ‖rhs‖ / lam := by
  have hsymbol :
      0 < ‖shiftedEllipticSymbol1D lam ξ‖ :=
    norm_pos_iff.mpr (shiftedEllipticSymbol1D_ne_zero_of_pos
      (lam := lam) (ξ := ξ) hpos)
  rw [norm_div]
  apply (div_le_iff₀ hsymbol).2
  calc
    ‖rhs‖ = (‖rhs‖ / lam) * lam := by
      rw [div_mul_cancel₀]
      exact hpos.ne'
    _ ≤ (‖rhs‖ / lam) * ‖shiftedEllipticSymbol1D lam ξ‖ := by
      exact mul_le_mul_of_nonneg_left
        (shiftedEllipticSymbol1D_le_norm (lam := lam) (ξ := ξ) hpos)
        (div_nonneg (norm_nonneg rhs) hpos.le)

/-- Pointwise transform-domain solution formula for
`(-∂ₓₓ + λ)u = f` when `λ > 0`. -/
theorem fourier_shifted_elliptic_equation_iff (u f : 𝓢(ℝ, ℂ)) {lam : ℝ}
    (hpos : 0 < lam) (x : ℝ) :
    SchwartzMap.fourierTransformCLM ℂ
        (-(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ u)) +
          (lam : ℂ) • u) x =
        SchwartzMap.fourierTransformCLM ℂ f x ↔
      SchwartzMap.fourierTransformCLM ℂ u x =
        SchwartzMap.fourierTransformCLM ℂ f x /
          shiftedEllipticSymbol1D lam x := by
  rw [fourier_shifted_negative_second_derivative_multiplier]
  have hsymbol :=
    shiftedEllipticSymbol1D_ne_zero_of_pos (lam := lam) (ξ := x) hpos
  constructor
  · intro h
    exact (eq_div_iff hsymbol).2 (by simpa [mul_comm] using h)
  · intro h
    rw [h]
    exact shiftedEllipticSymbol1D_mul_div
      (SchwartzMap.fourierTransformCLM ℂ f x) hpos

/-- Any Schwartz solution of the shifted elliptic equation satisfies the pointwise Fourier bound
`|û(ξ)| ≤ |f̂(ξ)| / λ`, uniformly in the frequency. -/
theorem fourier_shifted_elliptic_solution_norm_le (u f : 𝓢(ℝ, ℂ)) {lam : ℝ}
    (hpos : 0 < lam)
    (hEquation :
      -(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ u)) +
          (lam : ℂ) • u = f)
    (x : ℝ) :
    ‖SchwartzMap.fourierTransformCLM ℂ u x‖ ≤
      ‖SchwartzMap.fourierTransformCLM ℂ f x‖ / lam := by
  have hEquationAt :
      SchwartzMap.fourierTransformCLM ℂ
          (-(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ u)) +
            (lam : ℂ) • u) x =
        SchwartzMap.fourierTransformCLM ℂ f x :=
    congrArg (fun g : 𝓢(ℝ, ℂ) ↦
      SchwartzMap.fourierTransformCLM ℂ g x) hEquation
  rw [(fourier_shifted_elliptic_equation_iff u f hpos x).1 hEquationAt]
  exact norm_div_shiftedEllipticSymbol1D_le
    (SchwartzMap.fourierTransformCLM ℂ f x) hpos

end PDE.Elliptic.Classical.OneDimensional.Fourier
