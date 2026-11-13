/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Periodic.Definitions
public import PDE.Spaces.Sobolev.Periodic.Poincare

/-!
# Reconstruction from limits of periodic gradients

On the mean-zero periodic Sobolev space `meanZeroSpace n` the gradient map `meanZeroGradientCLM n`
is injective and has closed range (`meanZeroGradientCLM_injective`,
`isClosed_range_meanZeroGradientCLM`), so an `L²` limit of gradients of mean-zero periodic Sobolev
functions is the gradient of exactly one such function. The Poincaré inequality
`‖v - ⨍ v‖_{L²} ≤ ‖∇u‖_{L²}`, where `v` is the value of `u`, holds on the whole periodic Sobolev
graph `h1Space n` (`norm_value_sub_mean_le_gradient`).

## How it works

We start from the inequality `‖u‖_{L²} ≤ ‖∇u‖_{L²}` for a continuous potential `u` with continuous
coordinate derivatives and integral zero (`norm_toLp_le_gradient`, proved in
`PDE.Spaces.Sobolev.Periodic.Poincare` by comparing Fourier coefficients). The pairs `(v, w)` of the
ambient product with `‖v - ⨍ v‖ ≤ ‖w‖` form a closed set. It contains the graph point of every
continuous potential `u`, because `u - ⨍ u` has the same gradient and integral zero, so it contains
their closure `h1Space n`. On `meanZeroSpace n` the mean vanishes, and the Hilbert graph norm, which
adds the squared value and gradient norms, is at most twice the gradient norm
(`norm_le_two_mul_gradient`). Mathlib's `ContinuousLinearMap.antilipschitz_of_bound` makes the
gradient map antilipschitz, hence injective, and since `meanZeroSpace n` is complete
`AntilipschitzWith.isClosed_range` closes its range.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal NNReal Topology InnerProductSpace

namespace SobolevSpace.Periodic

/-- The mean of the `L²` class of a continuous function `u` is `∫ x, u x ∂cellMeasure n`. -/
theorem meanCLM_toLp {n : ℕ} (u : C(UnitAddTorus (Fin n), ℝ)) :
    meanCLM n (ContinuousMap.toLp 2 (cellMeasure n) ℝ u) =
      ∫ x, u x ∂cellMeasure n := by
  rw [meanCLM_apply]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (cellMeasure n) u)

/-- Subtracting the mean gives a periodic Sobolev potential with integral zero. -/
def meanZeroOfContinuous {n : ℕ}
    (u : C(UnitAddTorus (Fin n), ℝ)) (g : C(UnitAddTorus (Fin n), ℝ^n))
    (hd : ∀ x i t, HasDerivAt (fun s ↦ u (x + coordinateShift i s))
      (g (x + coordinateShift i t) i) t) : meanZeroSpace n := by
  let b := u - ContinuousMap.const _ (∫ x, u x ∂cellMeasure n)
  have hb : ∀ x i t, HasDerivAt (fun s ↦ b (x + coordinateShift i s))
      (g (x + coordinateShift i t) i) t := fun x i t ↦ (hd x i t).sub_const _
  refine ⟨ofContinuous b g hb, ?_⟩
  change meanCLM n (ContinuousMap.toLp 2 (cellMeasure n) ℝ b) = 0
  rw [meanCLM_toLp]
  simpa [b, average_eq_integral] using integral_sub_average (cellMeasure n) u

/-- The gradient of the centered potential `meanZeroOfContinuous u g hd` is the `L²` class of
`g`. -/
@[simp] theorem meanZeroGradientCLM_meanZeroOfContinuous {n : ℕ}
    (u : C(UnitAddTorus (Fin n), ℝ)) (g : C(UnitAddTorus (Fin n), ℝ^n))
    (hd : ∀ x i t, HasDerivAt (fun s ↦ u (x + coordinateShift i s))
      (g (x + coordinateShift i t) i) t) :
    meanZeroGradientCLM n (meanZeroOfContinuous u g hd) =
      ContinuousMap.toLp 2 (cellMeasure n) ℝ g := rfl

/-- Every `u ∈ h1Space n` satisfies `‖v - ⨍ v‖_{L²} ≤ ‖∇u‖_{L²}`, where `v = valueCLM n u`,
`⨍ v = meanCLM n v` and `∇u = gradientCLM n u`. -/
theorem norm_value_sub_mean_le_gradient {n : ℕ} (u : h1Space n) :
    ‖valueCLM n u - Lp.const 2 (cellMeasure n) (meanCLM n (valueCLM n u))‖ ≤
      ‖gradientCLM n u‖ := by
  let C : AmbientSpace n →L[ℝ] Lp ℝ 2 (cellMeasure n) :=
    WithLp.fstL 2 ℝ _ _ -
      ((Lp.constL 2 (cellMeasure n) ℝ).comp (meanCLM n)).comp (WithLp.fstL 2 ℝ _ _)
  have hclosed : IsClosed {v : AmbientSpace n | ‖C v‖ ≤ ‖v.snd‖} :=
    isClosed_le C.continuous.norm (WithLp.sndL 2 ℝ _ _).continuous.norm
  apply closure_minimal (t := {v : AmbientSpace n | ‖C v‖ ≤ ‖v.snd‖}) ?_ hclosed u.property
  rintro v ⟨a, g, hg, rfl⟩
  let b := a - ContinuousMap.const _ (∫ x, a x ∂cellMeasure n)
  have hb : ∀ x i t, HasDerivAt (fun s ↦ b (x + coordinateShift i s))
      (g (x + coordinateShift i t) i) t := fun x i t ↦ (hg x i t).sub_const _
  have hm : (∫ x, b x ∂cellMeasure n) = 0 := by
    simpa [b, average_eq_integral] using integral_sub_average (cellMeasure n) a
  have he : C (WithLp.toLp 2
      (ContinuousMap.toLp 2 (cellMeasure n) ℝ a,
        ContinuousMap.toLp 2 (cellMeasure n) ℝ g)) =
      ContinuousMap.toLp 2 (cellMeasure n) ℝ b := by
    change ContinuousMap.toLp 2 (cellMeasure n) ℝ a -
      Lp.const 2 (cellMeasure n) (meanCLM n (ContinuousMap.toLp 2 (cellMeasure n) ℝ a)) = _
    rw [meanCLM_toLp]
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (ContinuousMap.toLp 2 (cellMeasure n) ℝ a)
      (Lp.const 2 (cellMeasure n) (∫ x, a x ∂cellMeasure n)),
      ContinuousMap.coeFn_toLp (μ := cellMeasure n) (p := 2) (𝕜 := ℝ) a,
      ContinuousMap.coeFn_toLp (μ := cellMeasure n) (p := 2) (𝕜 := ℝ) b,
      Lp.coeFn_const 2 (cellMeasure n) (∫ x, a x ∂cellMeasure n)] with x hx ha hb hc
    rw [hx, Pi.sub_apply, ha, hb, hc]
    rfl
  change ‖C _‖ ≤ ‖ContinuousMap.toLp 2 (cellMeasure n) ℝ g‖
  rw [he]
  exact norm_toLp_le_gradient b g hb hm

/-- Every `u ∈ meanZeroSpace n` satisfies `‖valueCLM n u‖_{L²} ≤ ‖∇u‖_{L²}`. -/
theorem norm_value_le_gradient {n : ℕ} (u : meanZeroSpace n) :
    ‖valueCLM n u.val‖ ≤ ‖meanZeroGradientCLM n u‖ := by
  have hm : meanCLM n (valueCLM n u.val) = 0 := u.property
  change ‖valueCLM n u.val‖ ≤ ‖gradientCLM n u.val‖
  simpa [hm] using norm_value_sub_mean_le_gradient u.val

/-- Every `u ∈ meanZeroSpace n` has graph norm at most `2 ‖∇u‖_{L²}`. -/
theorem norm_le_two_mul_gradient {n : ℕ} (u : meanZeroSpace n) :
    ‖u‖ ≤ 2 * ‖meanZeroGradientCLM n u‖ := by
  have hp := norm_value_le_gradient u
  have hn := WithLp.prod_norm_sq_eq_of_L2 u.val.val
  change ‖u‖ ^ 2 = ‖valueCLM n u.val‖ ^ 2 + ‖meanZeroGradientCLM n u‖ ^ 2 at hn
  nlinarith [norm_nonneg u, norm_nonneg (valueCLM n u.val),
    norm_nonneg (meanZeroGradientCLM n u)]

/-- The gradient map on `meanZeroSpace n` has closed range: an `L²` limit of gradients of
mean-zero periodic Sobolev functions is the gradient of a mean-zero periodic Sobolev function. -/
theorem isClosed_range_meanZeroGradientCLM (n : ℕ) :
    IsClosed (Set.range (meanZeroGradientCLM n)) :=
  ((meanZeroGradientCLM n).antilipschitz_of_bound
    (K := (2 : ℝ≥0)) norm_le_two_mul_gradient).isClosed_range
      (meanZeroGradientCLM n).uniformContinuous

/-- The gradient map on `meanZeroSpace n` is injective: a mean-zero periodic Sobolev function is
determined by its gradient. -/
theorem meanZeroGradientCLM_injective (n : ℕ) :
    Function.Injective (meanZeroGradientCLM n) :=
  ((meanZeroGradientCLM n).antilipschitz_of_bound
    (K := (2 : ℝ≥0)) norm_le_two_mul_gradient).injective

end SobolevSpace.Periodic
