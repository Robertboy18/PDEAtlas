/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.GaussianRegularization.Entire
public import PDE.Analysis.Normed.Algebra.Exponential.NormBound

/-!
# Gaussian Fourier bounds for operator exponentials

The amplitude is the exponential of an affine operator pencil. Its
holomorphy and growth are derived in the Banach algebra, with no spectral or
commutation premise. The zero algebra is included.
-/

@[expose] public noncomputable section

open MeasureTheory Complex

namespace PDE.Analysis.Fourier

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Gaussian Fourier decay for an affine operator exponential,
including pencils whose constant and linear parts do not commute. -/
theorem norm_integral_gaussian_phase_exp_le
    (h₁ : ‖(1 : A)‖ ≤ 1) (R S : A) {b : ℝ} (hb : 0 < b) (k : ℝ) :
    ‖∫ x : ℝ, Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2 + (k : ℂ) * I * x) •
      NormedSpace.exp (R + (x : ℂ) • S)‖ ≤
      Real.exp ‖R‖ * √(Real.pi / (b / 2)) *
        Real.exp (-(k ^ 2 / (4 * b)) + ‖S‖ * |k / (2 * b)| + ‖S‖ ^ 2 / (2 * b)) := by
  have hexp : Differentiable ℂ (NormedSpace.exp : A → A) :=
    fun x ↦ (NormedSpace.exp_analytic (𝕂 := ℂ) x).differentiableAt
  apply norm_integral_gaussian_phase_smul_le (f := fun z ↦ NormedSpace.exp (R + z • S))
    (by fun_prop) hb (norm_nonneg S) (Real.exp_pos ‖R‖).le
  exact NormedSpace.norm_exp_add_smul_le h₁ R S

end PDE.Analysis.Fourier
