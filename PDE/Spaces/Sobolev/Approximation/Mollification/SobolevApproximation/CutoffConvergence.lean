/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.Cutoff
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.LpTail
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Convergence under expanding cutoffs

Truncation preserves an `Lᵖ` limit when the cutoff radius tends to infinity. Positive-order
cutoff derivatives instead kill every uniformly `Lᵖ`-bounded family. The two estimates
separate the principal term and the derivative terms in Sobolev approximation.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.Approximation

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {n : ℕ} {p : ℝ≥0∞}

/-- `Lᵖ` tails vanish along any radii tending to infinity. -/
theorem tendsto_eLpNorm_indicator_compl_closedBall_of_tendsto
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {f : ℝ^n → ℝ} (hf : MemLp f p volume)
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) :
    Tendsto (fun m ↦ eLpNorm ((Metric.closedBall (0 : ℝ^n) (R m))ᶜ.indicator f) p volume)
      atTop (𝓝 0) := by
  have hnat := tendsto_eLpNorm_indicator_compl_closedBall p hp hf
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ENNReal.tendsto_nhds_zero.mp hnat ε hε)
  filter_upwards [hR.eventually (eventually_ge_atTop (N : ℝ))] with m hm
  refine le_trans ?_ (hN N le_rfl)
  apply eLpNorm_mono (hf.aestronglyMeasurable.indicator measurableSet_closedBall.compl)
  intro x
  have hs := compl_subset_compl.mpr
    (Metric.closedBall_subset_closedBall (x := (0 : ℝ^n)) hm)
  by_cases hx : x ∈ (Metric.closedBall (0 : ℝ^n) (R m))ᶜ
  · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hs hx), le_refl]
  · simp only [Set.indicator_of_notMem hx, norm_zero, norm_nonneg]

/-- Expanding smooth cutoffs preserve the limit of an `Lᵖ`-convergent family. -/
theorem tendsto_eLpNorm_cutoff_mul_sub [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : ℝ^n → ℝ} (hf : MemLp f p volume) {v : ℕ → ℝ^n → ℝ}
    (hv : ∀ m, AEStronglyMeasurable (v m) volume)
    (hlim : Tendsto (fun m ↦ eLpNorm (fun x ↦ v m x - f x) p volume) atTop (𝓝 0))
    {R : ℕ → ℝ} (hRpos : ∀ m, 0 < R m) (hR : Tendsto R atTop atTop) :
    Tendsto (fun m ↦ eLpNorm (fun x ↦ cutoff (R m) x * v m x - f x) p volume)
      atTop (𝓝 0) := by
  have htail := tendsto_eLpNorm_indicator_compl_closedBall_of_tendsto hp hf hR
  have hbound (m : ℕ) :
      eLpNorm (fun x ↦ cutoff (R m) x * v m x - f x) p volume ≤
        eLpNorm (fun x ↦ v m x - f x) p volume +
          eLpNorm ((Metric.closedBall (0 : ℝ^n) (R m))ᶜ.indicator f) p volume := by
    have hsplit : (fun x ↦ cutoff (R m) x * v m x - f x) =
        (fun x ↦ cutoff (R m) x * (v m x - f x)) +
          (fun x ↦ (cutoff (R m) x - 1) * f x) := by funext x; dsimp; ring
    rw [hsplit]
    refine (eLpNorm_add_le (Fact.out : 1 ≤ p)).trans (add_le_add ?_ ?_)
    · apply eLpNorm_mono ((cutoff_contDiff (R m)).continuous.aestronglyMeasurable.mul
        ((hv m).sub hf.aestronglyMeasurable))
      intro x
      simpa only [Pi.mul_apply, Pi.sub_apply, norm_mul, Real.norm_eq_abs, one_mul] using
        mul_le_mul_of_nonneg_right (cutoff_abs_le_one (R m) x) (abs_nonneg (v m x - f x))
    · apply eLpNorm_mono (((cutoff_contDiff (R m)).continuous.aestronglyMeasurable.sub
        aestronglyMeasurable_const).mul hf.aestronglyMeasurable)
      intro x
      by_cases hx : x ∈ Metric.closedBall (0 : ℝ^n) (R m)
      · simp [cutoff_eq_one_of_mem_closedBall (hRpos m) hx, hx]
      · have hc : |cutoff (R m) x - 1| ≤ 1 := by
          rw [abs_of_nonpos (sub_nonpos.mpr (cutoff_le_one (R m) x))]
          linarith [cutoff_nonneg (R m) x]
        simpa [hx, norm_mul, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_right hc (abs_nonneg (f x))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hlim.add htail) (fun _ ↦ bot_le) hbound

/-- A positive-order cutoff derivative times a uniformly `Lᵖ`-bounded family vanishes.
Only the radius and the uniform bound enter; the family need not be a mollification. -/
theorem tendsto_eLpNorm_iteratedPartialDeriv_cutoff_mul
    (β : List (Fin n)) (hβ : β ≠ []) {R : ℕ → ℝ}
    (hRpos : ∀ m, 0 < R m) (hR : Tendsto R atTop atTop)
    {v : ℕ → ℝ^n → ℝ} (hv : ∀ m, AEStronglyMeasurable (v m) volume)
    {B : ℝ≥0∞} (hBfin : B ≠ ∞) (hB : ∀ m, eLpNorm (v m) p volume ≤ B) :
    Tendsto (fun m ↦ eLpNorm (fun x ↦ iteratedPartialDeriv β (cutoff (R m)) x * v m x)
      p volume) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_abs_iteratedPartialDeriv_cutoff_le β
  have hpow : Tendsto (fun m ↦ (R m)⁻¹ ^ β.length) atTop (𝓝 (0 : ℝ)) := by
    simpa [zero_pow (List.length_pos_of_ne_nil hβ).ne'] using
      (tendsto_inv_atTop_zero.comp hR).pow β.length
  have hcoef : Tendsto (fun m ↦ ENNReal.ofReal (C * (R m)⁻¹ ^ β.length)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul hpow)
  have hupper := ENNReal.Tendsto.mul_const hcoef (Or.inr hBfin)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hupper) (fun _ ↦ bot_le) fun m ↦ ?_
  have hmeas := ((PDE.contDiff_top_iteratedPartialDeriv
    (cutoff_contDiff (R m)) β).continuous.aestronglyMeasurable).mul (hv m)
  refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas
    (Eventually.of_forall fun x ↦ ?_) p).trans (mul_le_mul_right (hB m) _)
  simpa only [Pi.mul_apply, norm_mul, Real.norm_eq_abs, inv_pow] using
    mul_le_mul_of_nonneg_right (hC (R m) (hRpos m) x) (abs_nonneg (v m x))

end SobolevSpace.Approximation
