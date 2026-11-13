/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# A model identity for Laplace's method

For `λ > 0`, `laplaceConstantAmplitudeIntegral_eq` computes `√λ ∫ exp (-λ x²) c dx = √π c`
with Mathlib's `integral_gaussian`. This is the simplest case of Laplace's method, with
constant amplitude and quadratic phase. Evans, §4.5.2, states Laplace's method as the limit
(24) of a ratio of two such integrals, in which this Gaussian constant cancels.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.2, the lemma (Asymptotics), (24), and its proof,
  p. 217. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis.Asymptotics

open MeasureTheory

/-- The normalized constant-amplitude Gaussian integral used in the model Laplace method. -/
noncomputable def laplaceConstantAmplitudeIntegral (c lam : ℝ) : ℝ :=
  √lam * ∫ x : ℝ, Real.exp (-(lam * x ^ 2)) * c

/-- Exact normalized Gaussian identity behind the constant-amplitude Laplace-method model. -/
theorem laplaceConstantAmplitudeIntegral_eq (c : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    laplaceConstantAmplitudeIntegral c lam = √Real.pi * c := by
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  have hlam_nonneg : 0 ≤ lam := le_of_lt hlam
  have hgauss : ∫ x : ℝ, Real.exp (-(lam * x ^ 2)) = √(Real.pi / lam) := by
    simpa [neg_mul] using (integral_gaussian lam)
  have hmul : lam * (Real.pi / lam) = Real.pi := by
    field_simp [hlam0]
  calc
    laplaceConstantAmplitudeIntegral c lam =
        √lam * ((∫ x : ℝ, Real.exp (-(lam * x ^ 2))) * c) := by
          rw [laplaceConstantAmplitudeIntegral, integral_mul_const]
    _ = √lam * (√(Real.pi / lam) * c) := by
          rw [hgauss]
    _ = (√lam * √(Real.pi / lam)) * c := by ring
    _ = √(lam * (Real.pi / lam)) * c := by
          rw [← Real.sqrt_mul hlam_nonneg]
    _ = √Real.pi * c := by
          rw [hmul]

end PDE.Analysis.Asymptotics
