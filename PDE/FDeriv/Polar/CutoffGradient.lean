/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Polar.Profile
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Gradient bounds for a radial cutoff of a homogeneous polar field

The radial derivative includes the derivative of the cutoff. Orthogonality
of the radial and angular directions gives an exact squared-norm formula.

## Main results

* `norm_gradient_profileFromPolar_cutoff_rpow_mul_sq`: for `F = χ(r) r^m f(β)`,
  `|∇F|² = r^{2(m-1)} (((r χ'(r) + m χ(r)) f(β))² + (χ(r) f'(β))²)`.
* `norm_gradient_profileFromPolar_cutoff_rpow_mul_le`: from `|χ| ≤ C`, `|r χ'| ≤ B`, `|f| ≤ F`
  and `|f'| ≤ D`, `|∇F| ≤ r^{m-1} (((B + |m| C) F)² + (C D)²)^{1/2}`.
-/

@[expose] public noncomputable section

namespace PDE.FDeriv

open PDE.CoordinateSystems
open scoped Gradient

/-- For `χ` differentiable at `r`, `f` differentiable at `β` and `(r, β)` in the target of
`polarCoord`, the Cartesian partial derivatives of the polar profile `χ(s) s^m f(θ)` at the point
with polar coordinates `(r, β)` are
`∂₀ = r^(m-1) ((r χ'(r) + m χ(r)) f(β) cos β - χ(r) f'(β) sin β)` and
`∂₁ = r^(m-1) ((r χ'(r) + m χ(r)) f(β) sin β + χ(r) f'(β) cos β)`. -/
private theorem partialDeriv_cutoff_rpow_mul
    (m : ℝ) {χ f : ℝ → ℝ} {r β : ℝ}
    (hχ : DifferentiableAt ℝ χ r) (hf : DifferentiableAt ℝ f β)
    (hp : (r, β) ∈ polarCoord.target) :
    (∂[0] (profileFromPolar (fun s θ ↦ χ s * (s ^ m * f θ))))
        (planarPolarPoint r β) =
      r ^ (m - 1) * ((r * deriv χ r + m * χ r) * f β * Real.cos β -
        χ r * deriv f β * Real.sin β) ∧
    (∂[1] (profileFromPolar (fun s θ ↦ χ s * (s ^ m * f θ))))
        (planarPolarPoint r β) =
      r ^ (m - 1) * ((r * deriv χ r + m * χ r) * f β * Real.sin β +
        χ r * deriv f β * Real.cos β) := by
  have hr : 0 < r := hp.1
  have hround : polarCoord (pointPair (planarPolarPoint r β)) = (r, β) := by
    rw [pointPair_polarPoint_eq_polarCoord_symm]
    exact polarCoord.right_inv hp
  have hF := (hχ.hasDerivAt.comp_hasFDerivAt (r, β) (hasFDerivAt_fst (𝕜 := ℝ))).mul
    (((hasFDerivAt_fst (𝕜 := ℝ) (p := (r, β))).rpow_const
      (p := m) (Or.inl hr.ne')).mul
        (hf.hasDerivAt.comp_hasFDerivAt (r, β) (hasFDerivAt_snd (𝕜 := ℝ))))
  have hpolar := polarCoord_hasFDerivAt_symm_point hp
  rw [← pointPair_polarPoint_eq_polarCoord_symm r β] at hpolar
  rw [← hround] at hF
  have hx := partialDeriv_profileFromPolar_eq
    (fun s θ ↦ χ s * (s ^ m * f θ)) (planarPolarPoint r β) 0 hF hpolar
  have hy := partialDeriv_profileFromPolar_eq
    (fun s θ ↦ χ s * (s ^ m * f θ)) (planarPolarPoint r β) 1 hF hpolar
  have hpow : r ^ m = r ^ (m - 1) * r := by
    simpa only [sub_add_cancel] using Real.rpow_add_one hr.ne' (m - 1)
  constructor
  · rw [hx]
    rw [hround]
    simp [polarCoordForwardFDeriv, pointPairLinearMap,
      Matrix.toLin_finTwoProd_apply, hpow]
    field_simp [hr.ne']
    ring
  · rw [hy]
    rw [hround]
    simp [polarCoordForwardFDeriv, pointPairLinearMap,
      Matrix.toLin_finTwoProd_apply, hpow]
    field_simp [hr.ne']
    ring

/-- The squared gradient norm keeps the cutoff derivative in the radial component. -/
theorem norm_gradient_profileFromPolar_cutoff_rpow_mul_sq
    (m : ℝ) {χ f : ℝ → ℝ} {r β : ℝ}
    (hχ : DifferentiableAt ℝ χ r) (hf : DifferentiableAt ℝ f β)
    (hp : (r, β) ∈ polarCoord.target) :
    ‖∇ (profileFromPolar (fun s θ ↦ χ s * (s ^ m * f θ)))
      (planarPolarPoint r β)‖ ^ 2 =
      (r ^ (m - 1)) ^ 2 *
        (((r * deriv χ r + m * χ r) * f β) ^ 2 + (χ r * deriv f β) ^ 2) := by
  obtain ⟨hx, hy⟩ := partialDeriv_cutoff_rpow_mul m hχ hf hp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
    gradient_apply_eq_partialDeriv, gradient_apply_eq_partialDeriv, hx, hy]
  calc
    _ = (r ^ (m - 1)) ^ 2 *
        (((r * deriv χ r + m * χ r) * f β) ^ 2 + (χ r * deriv f β) ^ 2) *
          (Real.cos β ^ 2 + Real.sin β ^ 2) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]

/-- Separate bounds on the cutoff and the angular factor give a Cartesian gradient bound. -/
theorem norm_gradient_profileFromPolar_cutoff_rpow_mul_le
    (m : ℝ) {χ f : ℝ → ℝ} {r β C B F D : ℝ}
    (hχ : DifferentiableAt ℝ χ r) (hf : DifferentiableAt ℝ f β)
    (hp : (r, β) ∈ polarCoord.target)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hcutoff : |χ r| ≤ C) (hcutoffDeriv : |r * deriv χ r| ≤ B)
    (hvalue : |f β| ≤ F) (hderiv : |deriv f β| ≤ D) :
    ‖∇ (profileFromPolar (fun s θ ↦ χ s * (s ^ m * f θ)))
      (planarPolarPoint r β)‖ ≤
      r ^ (m - 1) * Real.sqrt (((B + |m| * C) * F) ^ 2 + (C * D) ^ 2) := by
  have hr : 0 < r := hp.1
  have hradial : |r * deriv χ r + m * χ r| ≤ B + |m| * C := by
    calc
      _ ≤ |r * deriv χ r| + |m * χ r| := abs_add_le _ _
      _ ≤ _ := add_le_add hcutoffDeriv
        (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hcutoff (abs_nonneg _))
  have hradialValue : |(r * deriv χ r + m * χ r) * f β| ≤ (B + |m| * C) * F := by
    rw [abs_mul]
    exact mul_le_mul hradial hvalue (abs_nonneg _) (by positivity)
  have hangular : |χ r * deriv f β| ≤ C * D := by
    rw [abs_mul]
    exact mul_le_mul hcutoff hderiv (abs_nonneg _) hC
  have hradialSq := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hradialValue
  have hangularSq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC hD)).mpr hangular
  simp only [sq_abs] at hradialSq hangularSq
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_gradient_profileFromPolar_cutoff_rpow_mul_sq m hχ hf hp,
    mul_pow (r ^ (m - 1)) (Real.sqrt (((B + |m| * C) * F) ^ 2 + (C * D) ^ 2)) 2,
    Real.sq_sqrt (by positivity)]
  exact mul_le_mul_of_nonneg_left (add_le_add hradialSq hangularSq) (sq_nonneg _)

end PDE.FDeriv
