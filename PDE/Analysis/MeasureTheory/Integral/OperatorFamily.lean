/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.OperatorFamily
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrating strongly measurable operator families

A uniformly bounded family of continuous real linear maps defines a bounded
map from L1 into the output space by Bochner integration. Strong measurability
is required only after evaluation on each fixed vector. Mathlib's measurable
evaluation lemmas give integrability of the family applied to an L1 input.

The norm bound is inherited without a finite-measure assumption. The integral
and all almost-everywhere identifications use the actual Lp representatives.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A uniformly bounded, strongly measurable operator family takes integrable
inputs to integrable outputs: the case `p = 1` of `MemLp.operatorFamily`. No
measurability in operator norm is required. -/
theorem Integrable.apply_operatorFamily {f : α → E} (hf : Integrable f μ)
    (R : α → E →L[ℝ] F) (hR : ∀ v, AEStronglyMeasurable (fun s ↦ R s v) μ)
    {M : ℝ} (hbound : ∀ᵐ s ∂μ, ∀ v, ‖R s v‖ ≤ M * ‖v‖) :
    Integrable (fun s ↦ R s (f s)) μ :=
  memLp_one_iff_integrable.mp <| (memLp_one_iff_integrable.mpr hf).operatorFamily R hR
    (max M 0) <| hbound.mono fun s hs ↦ (R s).opNorm_le_bound (le_max_right M 0) fun v ↦
      (hs v).trans (mul_le_mul_of_nonneg_right (le_max_left M 0) (norm_nonneg v))

/-- Integrating a uniformly bounded operator family has the corresponding L1 bound. -/
theorem norm_integral_operatorFamily_le
    (R : α → E →L[ℝ] F) {M : ℝ}
    (hbound : ∀ᵐ s ∂μ, ∀ v, ‖R s v‖ ≤ M * ‖v‖) (f : Lp E 1 μ) :
    ‖∫ s, R s (f s) ∂μ‖ ≤ M * ‖f‖ := by
  calc
    _ ≤ ∫ s, M * ‖f s‖ ∂μ :=
      norm_integral_le_of_norm_le ((L1.integrable_coeFn f).norm.const_mul M)
        (hbound.mono fun s hs ↦ hs (f s))
    _ = _ := by rw [integral_const_mul, ← L1.norm_eq_integral_norm]

/-- The Bochner integral of a strongly measurable, uniformly bounded operator
family is a continuous linear map from L1 into its output space. -/
noncomputable def Lp.integralOperator
    (R : α → E →L[ℝ] F) (hR : ∀ v, AEStronglyMeasurable (fun s ↦ R s v) μ)
    {M : ℝ} (hbound : ∀ᵐ s ∂μ, ∀ v, ‖R s v‖ ≤ M * ‖v‖) : Lp E 1 μ →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∫ s, R s (f s) ∂μ
      map_add' := fun f g ↦ by
        calc
          _ = ∫ s, (R s (f s) + R s (g s)) ∂μ := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_add f g] with s hs
            rw [hs, Pi.add_apply, map_add]
          _ = _ := integral_add
            ((L1.integrable_coeFn f).apply_operatorFamily R hR hbound)
            ((L1.integrable_coeFn g).apply_operatorFamily R hR hbound)
      map_smul' := fun c f ↦ by
        simp only [RingHom.id_apply]
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with s hs
        rw [hs, Pi.smul_apply, map_smul] }
    M (norm_integral_operatorFamily_le R hbound)

/-- The integrated operator is given by the actual Bochner integral. -/
theorem Lp.integralOperator_apply
    (R : α → E →L[ℝ] F) (hR : ∀ v, AEStronglyMeasurable (fun s ↦ R s v) μ)
    {M : ℝ} (hbound : ∀ᵐ s ∂μ, ∀ v, ‖R s v‖ ≤ M * ‖v‖) (f : Lp E 1 μ) :
    Lp.integralOperator R hR hbound f = ∫ s, R s (f s) ∂μ := rfl

/-- The integrated operator inherits the uniform nonnegative bound. -/
theorem Lp.norm_integralOperator_le
    (R : α → E →L[ℝ] F) (hR : ∀ v, AEStronglyMeasurable (fun s ↦ R s v) μ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ s ∂μ, ∀ v, ‖R s v‖ ≤ M * ‖v‖) :
    ‖Lp.integralOperator R hR hbound‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _ hM (norm_integral_operatorFamily_le R hbound)

end MeasureTheory
