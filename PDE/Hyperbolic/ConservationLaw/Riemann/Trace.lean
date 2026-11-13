/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Riemann.Data
public import PDE.Hyperbolic.ConservationLaw.Scalar.InitialValue

/-!
# Strong traces from finite propagation

Every nonzero spatial point lies outside a finite propagation cone at
all sufficiently small positive times. Bounded measurable waves therefore
attain their two-state datum pointwise away from the jump. The
dominated-convergence criterion gives the strong local `L¹` trace, in an
arbitrary normed state space.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw

open Scalar

/-- Bounded measurable waves with constant exterior states outside a finite
propagation cone attain their Riemann datum strongly in local `L¹`. -/
theorem hasInitialTraceLocallyL1_riemannData_of_finitePropagation {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {u : ℝ^2 → E} {left right : E}
    {K M : ℝ} (hmeas : Measurable u) (hbound : ∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K)
    (hleft : ∀ p : ℝ^2, 0 < p 0 → p 1 < -M * p 0 → u p = left)
    (hright : ∀ p : ℝ^2, 0 < p 0 → M * p 0 ≤ p 1 → u p = right) :
    HasInitialTraceLocallyL1 u (riemannData left right) := by
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  apply hasInitialTraceLocallyL1_of_dominated
  · exact locallyIntegrable_riemannData left right
  · exact fun a b ↦ Eventually.of_forall fun t ↦
      ((hmeas.comp (by fun_prop : Measurable (fun x : ℝ ↦ (!₂[t, x] : ℝ^2)))).sub
        (measurable_riemannData left right)).aestronglyMeasurable
  · intro a b
    refine ⟨fun _ ↦ K + max ‖left‖ ‖right‖, integrableOn_const measure_Icc_lt_top.ne, ?_⟩
    filter_upwards [hpos] with t ht using Eventually.of_forall fun x ↦ (norm_sub_le _ _).trans
        (add_le_add (hbound !₂[t, x] ht) (norm_riemannData_le_max left right x))
  · have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with x hx
    have ht0 : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    rcases lt_or_gt_of_ne hx with hx | hx
    · have hfront : Tendsto (fun t : ℝ ↦ -M * t) (𝓝[>] 0) (𝓝 0) := by
        simpa only [mul_zero] using tendsto_const_nhds.mul ht0
      rw [riemannData_of_neg left right hx]
      apply tendsto_const_nhds.congr'
      filter_upwards [hpos, hfront.eventually (Ioi_mem_nhds hx)] with t ht hxt
      exact (hleft !₂[t, x] ht hxt).symm
    · have hfront : Tendsto (fun t : ℝ ↦ M * t) (𝓝[>] 0) (𝓝 0) := by
        simpa only [mul_zero] using tendsto_const_nhds.mul ht0
      rw [riemannData_of_nonneg left right hx.le]
      apply tendsto_const_nhds.congr'
      filter_upwards [hpos, hfront.eventually (Iio_mem_nhds hx)] with t ht hxt
      exact (hright !₂[t, x] ht hxt.le).symm

end PDE.Hyperbolic.ConservationLaw
