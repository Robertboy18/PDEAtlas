/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Radon.Backprojection
public import PDE.Analysis.Fourier.Radon.Schwartz
public import PDE.Analysis.Fourier.Schwartz.Derivatives

/-!
# Radon inversion by differentiation in odd dimensions

In dimension `2k + 1`, the backprojection filter is `|σ|^(2k) = σ^(2k)`.
It is therefore a local operation: take `2k` derivatives in the displacement,
then average over the unit normals. The coefficient is
`(-1)^k / (2 (2π)^(2k))`.

In three dimensions this becomes `-1/(8π²)` times the average of the second
displacement derivative. The sphere measure is induced by Euclidean volume;
it is not normalized to total mass one. Every derivative below is an ordinary
derivative of the hyperplane integral.

`eq_integral_iteratedDeriv_radonTransform` is Evans, §4.3.2, Theorem 5(ii), (33)-(34), with
the same coefficient; we derive it from `eq_integral_filtered_radonTransform`, since
`|σ|^(2k) = σ^(2k)`, rather than from (32).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.2, Theorem 5(ii), (33)-(34), p. 199, and step 2 of
  its proof, pp. 199-200. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap RealInnerProductSpace

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- In odd dimension, ordinary displacement derivatives and spherical
backprojection reconstruct a Schwartz function pointwise. -/
theorem eq_integral_iteratedDeriv_radonTransform (f : 𝓢(E, F)) (k : ℕ)
    (hdim : Module.finrank ℝ E = 2 * k + 1) (x : E) :
    f x = ((-1 : ℝ) ^ k / (2 * (2 * Real.pi) ^ (2 * k))) •
      ∫ θ : Metric.sphere (0 : E) 1,
        iteratedDeriv (2 * k) (PDE.Analysis.Fourier.radonTransform f (θ : E))
          ⟪(θ : E), x⟫ ∂(volume : Measure E).toSphere := by
  rw [f.eq_integral_filtered_radonTransform x, hdim, Nat.add_sub_cancel]
  have he (θ : Metric.sphere (0 : E) 1) :
      𝓕⁻ (fun σ : ℝ ↦ |σ| ^ (2 * k) •
        𝓕 (PDE.Analysis.Fourier.radonTransform f (θ : E)) σ) ⟪(θ : E), x⟫ =
      ((-1 : ℝ) ^ k / (2 * Real.pi) ^ (2 * k)) •
        iteratedDeriv (2 * k) (PDE.Analysis.Fourier.radonTransform f (θ : E))
          ⟪(θ : E), x⟫ := by
    simp_rw [(even_two_mul k).pow_abs]
    rw [← radonTransformCLM_apply (θ := (θ : E)) (by simp)]
    exact fourierInv_even_pow_smul_fourier _ k _
  simp_rw [he]
  rw [integral_smul, smul_smul]
  congr 1
  ring

/-- In dimension three, inversion is `-1/(8π²)` times the spherical
backprojection of the second displacement derivative. -/
theorem eq_integral_secondDeriv_radonTransform (f : 𝓢(E, F))
    (hdim : Module.finrank ℝ E = 3) (x : E) :
    f x = (-1 / (8 * Real.pi ^ 2) : ℝ) •
      ∫ θ : Metric.sphere (0 : E) 1,
        deriv (deriv (PDE.Analysis.Fourier.radonTransform f (θ : E)))
          ⟪(θ : E), x⟫ ∂(volume : Measure E).toSphere := by
  have h := f.eq_integral_iteratedDeriv_radonTransform 1 hdim x
  norm_num [iteratedDeriv_succ, iteratedDeriv_zero] at h
  convert h using 1
  congr 2
  ring

end SchwartzMap
