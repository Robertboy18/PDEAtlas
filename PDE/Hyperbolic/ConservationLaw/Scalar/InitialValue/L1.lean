/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.InitialValue

/-!
# Global L¹ initial convergence implies the local trace

The definition of entropy solution in Evans, §11.4.3, asks for `u ∈ C([0, ∞), L¹(ℝ))` with
`u(·, t) → g` in `L¹` as `t → 0`. This global L¹ initial condition implies the local initial
trace used by the contraction theorem. We also give the implication directly from a continuous
L¹ curve, allowing arbitrary almost-everywhere representatives of each spatial slice.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, definition of entropy solution.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter MeasureTheory Set PDE.Common
open scoped Topology NNReal

namespace PDE.Hyperbolic.ConservationLaw.Scalar

variable {E : Type*} [NormedAddCommGroup E] {u : ℝ^2 → E} {u₀ : ℝ → E}

/-- Global L¹ convergence to the datum implies strong local L¹ attainment of that datum.
Eventual integrability ensures that the displayed norm integrals are meaningful. -/
theorem hasInitialTraceLocallyL1_of_tendsto_integral_norm_sub (h₀ : Integrable u₀ volume)
    (hi : ∀ᶠ t : ℝ in 𝓝[>] 0, Integrable (fun x ↦ u !₂[t, x] - u₀ x) volume)
    (hlim : Tendsto (fun t : ℝ ↦ ∫ x : ℝ, ‖u !₂[t, x] - u₀ x‖) (𝓝[>] 0) (𝓝 0)) :
    HasInitialTraceLocallyL1 u u₀ := by
  refine ⟨h₀.locallyIntegrable, fun a b ↦ ⟨hi.mono fun _ ht ↦ ht.integrableOn, ?_⟩⟩
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [hi] with t ht
  exact setIntegral_le_integral ht.norm (Eventually.of_forall fun _ ↦ norm_nonneg _)

/-- A continuous L¹ curve attains its initial value in the local trace sense.
The spacetime representative need only represent the curve on each spatial slice. -/
theorem hasInitialTraceLocallyL1_of_continuousAt_L1 (w : ℝ≥0 → Lp E 1 (volume : Measure ℝ))
    (hw : ContinuousAt w 0) (hrep : ∀ t : ℝ≥0, (fun x : ℝ ↦ u !₂[(t : ℝ), x]) =ᵐ[volume] w t)
    (h₀ : u₀ =ᵐ[volume] w 0) :
    HasInitialTraceLocallyL1 u u₀ := by
  have hslice (t : ℝ) (ht : 0 < t) :
      (fun x : ℝ ↦ u !₂[t, x]) =ᵐ[volume] w t.toNNReal := by
    simpa only [Real.coe_toNNReal t ht.le] using hrep t.toNNReal
  have hi : ∀ᶠ t : ℝ in 𝓝[>] 0, Integrable (fun x ↦ u !₂[t, x] - u₀ x) volume := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((L1.integrable_coeFn (w t.toNNReal)).sub (L1.integrable_coeFn (w 0))).congr
      ((hslice t ht).sub h₀).symm
  apply hasInitialTraceLocallyL1_of_tendsto_integral_norm_sub
    ((L1.integrable_coeFn (w 0)).congr h₀.symm) hi
  have hnn : Tendsto Real.toNNReal (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0)) := by
    simpa using (continuous_real_toNNReal.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have htime : Tendsto (fun t : ℝ ↦ w t.toNNReal) (𝓝[>] 0) (𝓝 (w 0)) := hw.tendsto.comp hnn
  have hdist : Tendsto (fun t : ℝ ↦ dist (w t.toNNReal) (w 0)) (𝓝[>] 0) (𝓝 0) := by
    simpa using htime.dist (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ w 0) (𝓝[>] 0) (𝓝 (w 0)))
  apply hdist.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [hslice t ht, h₀] with x hx hx₀
  simp only [hx, hx₀, dist_eq_norm]

end PDE.Hyperbolic.ConservationLaw.Scalar
