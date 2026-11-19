/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Weighted L² bounds from a dense set

Continuity into an ambient L² space yields an almost-everywhere convergent
subsequence. Fatou transfers a weighted estimate from a dense set to every
point, for any measure dominated by the ambient measure.
-/

@[expose] public noncomputable section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

/-- A weighted L² bound on a dense set extends along a continuous L² map. -/
theorem weighted_lp_bound_of_denseRange
    {E D X : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (η ν : Measure X) (hν : ν ≤ η)
    (v : D → E) (hv : DenseRange v) (L : E → Lp ℝ 2 η) (hL : Continuous L)
    (W : (X → ℝ)) (hW : AEStronglyMeasurable W ν) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ d, MemLp (fun x ↦ L (v d) x * √(W x)) 2 ν ∧
      lpNorm (fun x ↦ L (v d) x * √(W x)) 2 ν ≤ C * ‖v d‖) (U : E) :
    MemLp (fun x ↦ L U x * √(W x)) 2 ν ∧
      lpNorm (fun x ↦ L U x * √(W x)) 2 ν ≤ C * ‖U‖ := by
  obtain ⟨u, hu, hulim⟩ := mem_closure_iff_seq_limit.mp (hv U)
  choose d hd using hu
  have hflim : Tendsto (fun n ↦ v (d n)) atTop (𝓝 U) := by simpa only [hd] using hulim
  have hLlim := (hL.tendsto U).comp hflim
  obtain ⟨ns, hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hLlim).exists_seq_tendsto_ae
  let F (n : ℕ) : (X → ℝ) := fun x ↦ L (v (d (ns n))) x * √(W x)
  let g : (X → ℝ) := fun x ↦ L U x * √(W x)
  have hF (n : ℕ) : MemLp (F n) 2 ν ∧ lpNorm (F n) 2 ν ≤ C * ‖v (d (ns n))‖ :=
    hbound (d (ns n))
  have hlim' : ∀ᵐ x ∂ν, Tendsto (fun n ↦ F n x) atTop (𝓝 (g x)) := by
    filter_upwards [hlim.filter_mono (ae_mono hν)] with x hx
    exact hx.mul_const _
  have hg : AEStronglyMeasurable g ν :=
    ((Lp.memLp (L U)).aestronglyMeasurable.mono_measure hν).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hW)
  have hb := (hflim.comp hns.tendsto_atTop).norm.const_mul C
  have hnorm : eLpNorm g 2 ν ≤ ENNReal.ofReal (C * ‖U‖) := by
    calc
      _ ≤ atTop.liminf (fun n ↦ eLpNorm (F n) 2 ν) :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n ↦ (hF n).1.aestronglyMeasurable) g hg hlim'
      _ ≤ atTop.liminf (fun n ↦ ENNReal.ofReal (C * ‖v (d (ns n))‖)) :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n ↦ by
          rw [← ofReal_lpNorm (hF n).1]
          exact ENNReal.ofReal_le_ofReal (hF n).2)
      _ = _ := ((ENNReal.continuous_ofReal.tendsto (C * ‖U‖)).comp hb).liminf_eq
  refine ⟨hnorm.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg hC (norm_nonneg U)))

end MeasureTheory
