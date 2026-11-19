/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.TerminalClosure
import PDE.Analysis.MeasureTheory.Lp.CommonSupportConvergence

/-!
# Continuity of supported Sobolev trajectories

Joint continuity with a common compact support gives continuity of the L² base.
A bounded H² graph then gives joint continuity of the first spatial derivative
and of the normalized Hilbert velocity and its derivative.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open SobolevSpace SobolevSpace.GraphSpace
open scoped Topology Sobolev

namespace DeGregorio.Iteration

/-- Jointly continuous representatives with one compact support determine a
strongly continuous L² base curve. No norm continuity is supplied. -/
theorem continuous_base_of_common_compact_support
    {X : Type*} [TopologicalSpace X] {f : X → DerivLp 1 2 univ}
    {w : X → ℝ → ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hw : Continuous (fun p : ℝ × X ↦ w p.2 p.1))
    (hs : ∀ t, Function.support (w t) ⊆ K)
    (hrep : ∀ t, (oneDimensionalPushforwardL2 (f t) : ℝ → ℝ) =ᵐ[volume] w t) :
    Continuous f := by
  have hslice (t : X) : Continuous (w t) :=
    hw.comp (continuous_id.prodMk continuous_const)
  have hC : Continuous (fun t ↦ (⟨w t, hslice t⟩ : C(ℝ, ℝ))) :=
    ContinuousMap.continuous_of_continuous_uncurry _ (hw.comp continuous_swap)
  have hF : Continuous (fun t ↦ oneDimensionalPushforwardL2 (f t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
    have he := tendsto_eLpNorm_sub_of_tendstoUniformlyOn
      (by norm_num : (2 : ENNReal) ≠ ⊤) hK.measurableSet.nullMeasurableSet
      (hK.measure_lt_top (μ := volume)).ne
      (.of_forall fun s ↦ ((hslice s).sub (hslice t)).aestronglyMeasurable)
      (.of_forall hs) (hs t)
      ((ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
        (hC.tendsto t)) K hK)
    convert he using 1
    funext s
    exact eLpNorm_congr_ae ((hrep s).sub (hrep t))
  simpa only [Function.comp_def, oneDimensionalPullbackL2_pushforward] using
    oneDimensionalPullbackL2.continuous.comp hF

/-- Continuity on every shorter closed slab gives continuity on the half-open
slab, including its initial slice. -/
theorem continuous_halfOpen_of_closed_restrictions
    {w : ℝ → ℝ → ℝ} {a T : ℝ}
    (hw : ∀ s ∈ Ioo a T,
      Continuous (fun p : ℝ × Icc a s ↦ w p.1 p.2)) :
    Continuous (fun p : ℝ × Ico a T ↦ w p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨s, hts, hsT⟩ := exists_between p.2.property.2
  have has : a < s := p.2.property.1.trans_lt hts
  have hc : Continuous (fun q : ℝ × Ico a T ↦
      w q.1 (projIcc a s has.le q.2)) := (hw s ⟨has, hsT⟩).comp
    (continuous_fst.prodMk ((continuous_projIcc (h := has.le)).comp
      (continuous_subtype_val.comp continuous_snd)))
  apply hc.continuousAt.congr_of_eventuallyEq
  have htend := (continuous_subtype_val.comp continuous_snd).tendsto p
  filter_upwards [htend (Iio_mem_nhds hts)] with q hq
  simp only [projIcc_of_mem has.le (show (q.2 : ℝ) ∈ Icc a s from ⟨q.2.property.1, hq.le⟩)]

end DeGregorio.Iteration
