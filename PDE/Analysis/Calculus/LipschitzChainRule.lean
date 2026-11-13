/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic.Positivity.Finset
import PDE.Analysis.Calculus.NullPreimage

/-!
# Almost-everywhere chain rule for real Lipschitz maps

The scalar chain rule behind Sobolev Nemytskii operators holds for a
Lipschitz outer map. That map is differentiable almost everywhere by
Rademacher's theorem on the line, Mathlib's `LipschitzWith.ae_differentiableAt_real`. Above
its exceptional null set, the derivative of the inner function vanishes almost everywhere by
the null-preimage principle `ae_deriv_eq_zero_on_preimage_null`.

## Main results

* `LipschitzWith.ae_hasDerivAt_comp`, `LipschitzWith.ae_deriv_comp`: if `F` is Lipschitz and
  `f` is measurable and differentiable almost everywhere, then
  `(F ∘ f)' = F'(f) f'` almost everywhere.

## References

* M. Marcus and V. J. Mizel, "Absolute continuity on tracks and mappings of Sobolev spaces",
  *Arch. Rational Mech. Anal.* 45 (1972), no. 4, 294-320.
  <https://doi.org/10.1007/BF00251378>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped NNReal Topology

namespace PDE.Analysis.Calculus

private theorem hasDerivAt_comp_zero_of_lipschitz
    {F f : ℝ → ℝ} {C : ℝ≥0} {x : ℝ}
    (hF : LipschitzWith C F) (hf : HasDerivAt f 0 x) :
    HasDerivAt (F ∘ f) 0 x := by
  rw [hasDerivAt_iff_tendsto_slope_zero, Function.comp_def]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero
    (g := fun t ↦ (C : ℝ) * ‖t⁻¹ • (f (x + t) - f x)‖)
    (fun _ ↦ norm_nonneg _) (fun t ↦ ?_) ?_
  · rw [norm_smul, norm_smul]
    calc
      ‖t⁻¹‖ * ‖F (f (x + t)) - F (f x)‖
          ≤ ‖t⁻¹‖ * ((C : ℝ) * ‖f (x + t) - f x‖) :=
        mul_le_mul_of_nonneg_left (hF.norm_sub_le _ _) (norm_nonneg _)
      _ = (C : ℝ) * (‖t⁻¹‖ * ‖f (x + t) - f x‖) := by ring
  · have hnorm :
        Tendsto
          (fun t ↦ ‖t⁻¹ • (f (x + t) - f x)‖)
          (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      simpa using hf.tendsto_slope_zero.norm
    simpa using hnorm.const_mul (C : ℝ)

/-- A Lipschitz outer map composed with an almost-everywhere differentiable
measurable inner function has the expected derivative almost everywhere. -/
theorem LipschitzWith.ae_hasDerivAt_comp
    {F f : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hf : Measurable f)
    (hfdiff : ∀ᵐ x, DifferentiableAt ℝ f x) :
    ∀ᵐ x,
      HasDerivAt (F ∘ f) (deriv F (f x) * deriv f x) x := by
  let N : Set ℝ := {y | ¬ DifferentiableAt ℝ F y}
  have hN : MeasurableSet N :=
    (measurableSet_of_differentiableAt ℝ F).compl
  have hN0 : volume N = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hF.ae_differentiableAt_real] with y hy
    simpa [N] using hy
  have hzero := ae_deriv_eq_zero_on_preimage_null hf hN hN0
  filter_upwards [hfdiff, hzero] with x hfx hzero
  by_cases hFx : DifferentiableAt ℝ F (f x)
  · exact hFx.hasDerivAt.comp x hfx.hasDerivAt
  · have hinner0 : deriv f x = 0 := hzero hFx
    have hfzero : HasDerivAt f 0 x := by
      simpa [hinner0] using hfx.hasDerivAt
    simpa [hinner0] using
      hasDerivAt_comp_zero_of_lipschitz hF hfzero

/-- Almost-everywhere scalar chain rule for a Lipschitz outer map and an
almost-everywhere differentiable measurable inner function. -/
theorem LipschitzWith.ae_deriv_comp
    {F f : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hf : Measurable f)
    (hfdiff : ∀ᵐ x, DifferentiableAt ℝ f x) :
    ∀ᵐ x, deriv (F ∘ f) x = deriv F (f x) * deriv f x := by
  filter_upwards [
    PDE.Analysis.Calculus.LipschitzWith.ae_hasDerivAt_comp
      hF hf hfdiff] with x hx
  exact hx.deriv

end PDE.Analysis.Calculus
