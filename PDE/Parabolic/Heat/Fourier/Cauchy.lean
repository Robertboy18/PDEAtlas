/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import PDE.Parabolic.Heat.Fourier.Representation
public import PDE.Parabolic.Heat.PointwiseIVP
import PDE.Parabolic.Heat.ConvolutionSpace.Equation
import PDE.Parabolic.Heat.ConvolutionSpace.InitialContinuity
import PDE.Parabolic.Heat.ConvolutionSpace.JointSmoothness

/-!
# Classical heat solutions given by Fourier inversion

Let `g` be a bounded continuous integrable real function on `ℝⁿ`, and let `u` be the real part of
the inverse Fourier heat formula `fourierSolution`, `𝓕⁻¹(e^{-4π²t|ξ|²} 𝓕 g)`. Then `u` is jointly
smooth at positive times (`contDiffAt_fourierSolution_timeSpace`), solves `uₜ = Δu` there
(`deriv_fourierSolution_time_eq_laplacian`) and tends to `g(x)` as `(t, y) → (0, x)` with `t > 0`
(`fourierSolution_initial_trace`). When `𝓕 g` is also integrable, `u` takes the value `g` at time
zero and is a pointwise classical solution of the Cauchy problem
(`fourierSolution_isPointwiseInitialValueSolution`); Schwartz data need no further hypothesis
(`fourierSolution_schwartz_isPointwiseInitialValueSolution`).

## How it works

Evans's §4.3.1, Example 2, transforms the heat equation in the spatial variables, solves
`ûₜ + |y|²û = 0` to get `û = e^{-t|y|²} ĝ` and inverts the transform, which gives the heat kernel
formula (18). We do not start from a solution of the transformed equation. For `t > 0` we identify
the formula with the Gaussian convolution `initialValueSolution`
(`fourierSolution_ofReal_eq_initialValueSolution`) and take smoothness, the heat equation and the
initial trace from the convolution, so the trace needs no integrability of `𝓕 g`. At `t = 0` the
formula is `𝓕⁻¹ (𝓕 g)`, which is `g` by Fourier inversion when `𝓕 g` is integrable.

## Implementation notes

Mathlib's Fourier transform is `𝓕 g (ξ) = ∫ e^{-2πi⟨x, ξ⟩} g(x) dx`, so Evans's multiplier
`e^{-t|y|²}` becomes `e^{-4π²t|ξ|²}`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.1, Example 2 (Fundamental solution of heat equation),
  (16)-(18), p. 192.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped FourierTransform Topology BoundedContinuousFunction ContDiff SchwartzMap

namespace HeatEquation

variable {n : ℕ}

private theorem fourierSolution_re_eq {g : ℝ^n → ℝ} (hg : Integrable g)
    (x : ℝ^n) {t : ℝ} (ht : 0 < t) :
    (fourierSolution (fun y ↦ (g y : ℂ)) x t).re = initialValueSolution g x t :=
  congrArg Complex.re (fourierSolution_ofReal_eq_initialValueSolution hg x ht)

/-- The inverse Fourier heat formula is jointly smooth at positive time for
bounded continuous integrable real data. No derivative of the datum is required. -/
theorem contDiffAt_fourierSolution_timeSpace (g : ℝ^n →ᵇ ℝ) (hg : Integrable g)
    (x : ℝ^n) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ^n ↦ (fourierSolution (fun y ↦ (g y : ℂ)) p.2 p.1).re) (t, x) := by
  apply (contDiffAt_initialValueSolution_timeSpace g x t ht g.continuous
    ⟨‖g‖, fun y ↦ g.norm_coe_le_norm y⟩).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds ht] with p hp
  exact fourierSolution_re_eq hg p.2 hp

/-- The Fourier formula solves `u_t = Δu` using analytic derivatives.
Its joint smoothness at positive times is `contDiffAt_fourierSolution_timeSpace`. -/
theorem deriv_fourierSolution_time_eq_laplacian (g : ℝ^n →ᵇ ℝ) (hg : Integrable g)
    (x : ℝ^n) {t : ℝ} (ht : 0 < t) :
    deriv (fun s ↦ (fourierSolution (fun y ↦ (g y : ℂ)) x s).re) t =
      PDE.laplacian (fun z ↦ (fourierSolution (fun y ↦ (g y : ℂ)) z t).re) x := by
  have htime : (fun s ↦ (fourierSolution (fun y ↦ (g y : ℂ)) x s).re) =ᶠ[𝓝 t]
      fun s ↦ initialValueSolution g x s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact fourierSolution_re_eq hg x hs
  rw [htime.deriv_eq]
  simp_rw [fourierSolution_re_eq hg _ ht]
  exact deriv_initialValueSolution_time_eq_laplacian g x t ht g.continuous
    ⟨‖g‖, fun y ↦ g.norm_coe_le_norm y⟩

/-- The Fourier heat solution approaches the bounded continuous integrable datum
jointly from positive time. Integrability of the unweighted Fourier transform is
not needed for this limit. -/
theorem fourierSolution_initial_trace (g : ℝ^n →ᵇ ℝ) (hg : Integrable g) (x : ℝ^n) :
    Tendsto (fun p : ℝ × ℝ^n ↦ (fourierSolution (fun y ↦ (g y : ℂ)) p.2 p.1).re)
      (𝓝[{p : ℝ × ℝ^n | 0 < p.1}] (0, x)) (𝓝 (g x)) := by
  have hlim := (continuous_initialValueSolution_timeSpace g g.continuous
    ⟨‖g‖, fun y ↦ g.norm_coe_le_norm y⟩).continuousAt.tendsto
      (x := (0, x))
  simp only [initialValueSolution_of_t_eq_zero] at hlim
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (fourierSolution_re_eq hg p.2 hp).symm

/-- When the initial Fourier transform is also integrable, the inverse Fourier
formula satisfies the classical heat Cauchy problem, including its value at time
zero and the joint continuous initial trace. -/
theorem fourierSolution_isPointwiseInitialValueSolution
    (g : ℝ^n →ᵇ ℝ) (hg : Integrable g)
    (hfg : Integrable (𝓕 (fun y ↦ (g y : ℂ)))) :
    IsPointwiseInitialValueSolution (fun _ _ ↦ 0) g
      (fun x t ↦ (fourierSolution (fun y ↦ (g y : ℂ)) x t).re) := by
  have H := initialValueSolution_isPointwiseHomogeneousInitialValueSolution
    g g.continuous ⟨‖g‖, fun y ↦ g.norm_coe_le_norm y⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x t ht
    apply (H.differentiableAt_time x t ht).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact fourierSolution_re_eq hg x hs
  · intro x t ht
    simpa only [fourierSolution_re_eq hg _ ht] using H.differentiableAt_space x t ht
  · intro x t ht i
    simpa only [fourierSolution_re_eq hg _ ht] using
      H.differentiableAt_spatialPartial x t ht i
  · intro x t ht
    exact sub_eq_zero.mpr (deriv_fourierSolution_time_eq_laplacian g hg x ht)
  · intro x
    exact congrArg Complex.re (fourierSolution_initial_value
      (Complex.ofRealCLM.integrable_comp hg) hfg
      (Complex.continuous_ofReal.comp g.continuous).continuousAt)
  · intro x ε hε
    obtain ⟨δ, hδ, htrace⟩ := H.continuousAt_initialBoundary x ε hε
    refine ⟨δ, hδ, fun y t hy ht htδ ↦ ?_⟩
    rw [fourierSolution_re_eq hg y ht]
    exact htrace y t hy ht htδ

/-- Real Schwartz initial data give a classical heat solution by the inverse
Fourier multiplier formula, with no separate Fourier-integrability assumptions. -/
theorem fourierSolution_schwartz_isPointwiseInitialValueSolution (g : 𝓢(ℝ^n, ℝ)) :
    IsPointwiseInitialValueSolution (fun _ _ ↦ 0) g
      (fun x t ↦ (fourierSolution (fun y ↦ (g y : ℂ)) x t).re) := by
  apply fourierSolution_isPointwiseInitialValueSolution g.toBoundedContinuousFunction g.integrable
  exact (𝓕 (SchwartzMap.postcompCLM Complex.ofRealCLM g)).integrable

end HeatEquation
