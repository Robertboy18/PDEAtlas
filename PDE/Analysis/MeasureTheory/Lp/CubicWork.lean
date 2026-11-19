/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing
import CAS.ExactTactic

/-!
# Cubic work on finite-energy rows

A bounded coefficient multiplies two undifferentiated L² rows. A coefficient
linear in the state, with a uniform pointwise bound, therefore defines a
continuous cubic work functional. The measure may be
infinite and may already contain a spatial weight.

The finite-family estimate allows a separate measure and energy constant for
each row.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace Topology

namespace MeasureTheory.Lp

variable {X E : Type*} [MeasurableSpace X] {ν : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A pointwise linear, uniformly bounded coefficient as an L∞ class. -/
def coefficientCLM (b : E →ₗ[ℝ] X → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ U, AEStronglyMeasurable (b U) ν)
    (hb : ∀ U, ∀ᵐ x ∂ν, ‖b U x‖ ≤ B * ‖U‖) : E →L[ℝ] Lp ℝ ∞ ν :=
  let hmem U := memLp_top_of_bound (hm U) (B * ‖U‖) (hb U)
  ({ toFun U := (hmem U).toLp (b U)
     map_add' U V := by
       apply Lp.ext
       filter_upwards [(hmem (U + V)).coeFn_toLp,
         (hmem U).coeFn_toLp, (hmem V).coeFn_toLp,
         Lp.coeFn_add ((hmem U).toLp (b U)) ((hmem V).toLp (b V))] with x h hU hV hs
       rw [h, hs]
       simp only [Pi.add_apply, hU, hV, map_add]
     map_smul' t U := by
       apply Lp.ext
       filter_upwards [(hmem (t • U)).coeFn_toLp, (hmem U).coeFn_toLp,
         Lp.coeFn_smul t ((hmem U).toLp (b U))] with x h hU hs
       change ((hmem (t • U)).toLp (b (t • U)) : X → ℝ) x =
         (t • (hmem U).toLp (b U) : Lp ℝ ∞ ν) x
       rw [h, hs]
       simp only [Pi.smul_apply, hU, map_smul] } : E →ₗ[ℝ] Lp ℝ ∞ ν).mkContinuous B fun U ↦ by
    change ‖(hmem U).toLp (b U)‖ ≤ _
    rw [Lp.norm_toLp, eLpNorm_exponent_top (hm U)]
    exact (ENNReal.toReal_le_toReal (eLpNormEssSup_lt_top_of_ae_bound (hb U)).ne
      ENNReal.ofReal_ne_top).2
      (eLpNormEssSup_le_of_ae_bound (hb U)) |>.trans_eq
        (ENNReal.toReal_ofReal (mul_nonneg hB (norm_nonneg U)))

/-- The bounded coefficient class represents the original spatial formula. -/
theorem coefficientCLM_ae (b : E →ₗ[ℝ] X → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ U, AEStronglyMeasurable (b U) ν)
    (hb : ∀ U, ∀ᵐ x ∂ν, ‖b U x‖ ≤ B * ‖U‖) (U : E) :
    (coefficientCLM b hB hm hb U : X → ℝ) =ᵐ[ν] b U :=
  (memLp_top_of_bound (hm U) (B * ‖U‖) (hb U)).coeFn_toLp

/-- The uniform coefficient estimate survives passage to the L∞ quotient. -/
theorem norm_coefficientCLM_apply_le (b : E →ₗ[ℝ] X → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ U, AEStronglyMeasurable (b U) ν)
    (hb : ∀ U, ∀ᵐ x ∂ν, ‖b U x‖ ≤ B * ‖U‖) (U : E) :
    ‖coefficientCLM b hB hm hb U‖ ≤ B * ‖U‖ := by
  change ‖(memLp_top_of_bound (hm U) (B * ‖U‖) (hb U)).toLp (b U)‖ ≤ _
  rw [Lp.norm_toLp, eLpNorm_exponent_top (hm U)]
  exact (ENNReal.toReal_le_toReal (eLpNormEssSup_lt_top_of_ae_bound (hb U)).ne
    ENNReal.ofReal_ne_top).2
    (eLpNormEssSup_le_of_ae_bound (hb U)) |>.trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hB (norm_nonneg U)))

/-- The pairing is the absolutely integrable coefficient times
the square of the row, on an arbitrary weighted measure. -/
theorem inner_multiplier_eq_integral (b : Lp ℝ ∞ ν) (u : Lp ℝ 2 ν)
    (f : X → ℝ) (hb : (b : X → ℝ) =ᵐ[ν] f) :
    Integrable (fun x ↦ f x * (u x) ^ 2) ν ∧
      ⟪b • u, u⟫_ℝ = ∫ x, f x * (u x) ^ 2 ∂ν := by
  have heq : (fun x ↦ (b • u : Lp ℝ 2 ν) x * u x) =ᵐ[ν]
      fun x ↦ f x * (u x) ^ 2 := by
    filter_upwards [Lp.coeFn_lpSMul (r := 2) b u, hb] with x hx hbx
    simp only [smul_eq_mul, Pi.mul_apply] at hx
    rw [hx, hbx, pow_two, mul_assoc]
  refine ⟨((Lp.memLp (b • u)).integrable_mul (Lp.memLp u)).congr heq, ?_⟩
  rw [L2.inner_def]
  exact integral_congr_ae (by simpa only [Real.inner_apply, mul_comm] using heq)

/-- One row work is continuous in both its coefficient state and its finite-energy field. -/
theorem continuous_rowWork (b : E →L[ℝ] Lp ℝ ∞ ν) (u : E →L[ℝ] Lp ℝ 2 ν) :
    Continuous (fun U ↦ ⟪b U • u U, u U⟫_ℝ) := by
  let M := (ContinuousLinearMap.mul ℝ ℝ).holderL ν ∞ 2 2
  have heq (a : Lp ℝ ∞ ν) (v : Lp ℝ 2 ν) : M a v = a • v := by
    dsimp only [M]
    rw [ContinuousLinearMap.holderL_apply_apply]
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) a v,
      Lp.coeFn_lpSMul (r := 2) a v] with x h hx
    simpa only [ContinuousLinearMap.mul_apply', smul_eq_mul, Pi.mul_apply] using h.trans hx.symm
  have hc := (M.continuous.comp b.continuous).clm_apply u.continuous
  simpa only [Function.comp_apply, heq] using hc.inner u.continuous

/-- A coefficient bound controls work by the squared row norm. -/
theorem abs_rowWork_le (b : Lp ℝ ∞ ν) (u : Lp ℝ 2 ν) {B : ℝ}
    (hb : ‖b‖ ≤ B) :
    |⟪b • u, u⟫_ℝ| ≤ B * ‖u‖ ^ 2 := by
  calc
    _ ≤ ‖b‖ * ‖u‖ * ‖u‖ := Lp.abs_inner_lpSMul_le b u u
    _ = ‖b‖ * ‖u‖ ^ 2 := by rw [pow_two, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (sq_nonneg _)

/-- A finite family of bounded-coefficient pairings defines continuous cubic work.
The coefficient bound and the row energy bound may have independent constants;
each row may use a different measure. -/
theorem continuous_and_abs_sum_work_le
    {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (η : (i : ι) → κ i → Measure X)
    (b : ∀ i d, E →L[ℝ] Lp ℝ ∞ (η i d))
    (q : ∀ i d, E →L[ℝ] Lp ℝ 2 (η i d)) {B C : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i d U, ‖b i d U‖ ≤ B * ‖U‖)
    (he : ∀ U, (∑ i, ∑ d, ‖q i d U‖ ^ 2) ≤ C * ‖U‖ ^ 2) :
    Continuous (fun U ↦ ∑ i, ∑ d, ⟪b i d U • q i d U, q i d U⟫_ℝ) ∧
      ∀ U, |∑ i, ∑ d, ⟪b i d U • q i d U, q i d U⟫_ℝ| ≤
        B * C * ‖U‖ ^ 3 := by
  constructor
  · apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro d _
    exact continuous_rowWork (b i d) (q i d)
  · intro U
    calc
      _ ≤ ∑ i, ∑ d, |⟪b i d U • q i d U, q i d U⟫_ℝ| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i, ∑ d, B * ‖U‖ * ‖q i d U‖ ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun d _ ↦
          abs_rowWork_le (b i d U) (q i d U) (hb i d U)
      _ = B * ‖U‖ * (∑ i, ∑ d, ‖q i d U‖ ^ 2) := by
        simp only [← Finset.mul_sum]
      _ ≤ B * ‖U‖ * (C * ‖U‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (he U) (mul_nonneg hB (norm_nonneg U))
      _ = B * C * ‖U‖ ^ 3 := by cas

end MeasureTheory.Lp
