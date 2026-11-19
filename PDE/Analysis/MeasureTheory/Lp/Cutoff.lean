/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import PDE.Analysis.MeasureTheory.DominatedLp

/-!
# Cutoffs on Lp

Restriction to a measurable set, extended by zero, is a continuous linear
contraction on Lp. For finite exponents on the real line, moving the endpoint
of a half-line gives a jointly continuous action on time and the Lp input.
The proof uses dominated Lp convergence and the zero measure of the endpoint.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace MeasureTheory.Lp

variable {α E 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (𝕜) in
/-- Restriction to a measurable set, extended by zero, as a contraction on Lp. -/
noncomputable def indicatorCLM {s : Set α} (hs : MeasurableSet s) : Lp E p μ →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ (MemLp.indicator hs.nullMeasurableSet (Lp.memLp u)).toLp _
      map_add' := fun u v ↦ by
        apply Lp.ext
        filter_upwards [(MemLp.indicator hs.nullMeasurableSet (Lp.memLp (u + v))).coeFn_toLp,
          (MemLp.indicator hs.nullMeasurableSet (Lp.memLp u)).coeFn_toLp,
          (MemLp.indicator hs.nullMeasurableSet (Lp.memLp v)).coeFn_toLp,
          Lp.coeFn_add u v, Lp.coeFn_add
            ((MemLp.indicator hs.nullMeasurableSet (Lp.memLp u)).toLp _)
            ((MemLp.indicator hs.nullMeasurableSet (Lp.memLp v)).toLp _)] with x huv hu hv hsum hout
        by_cases hx : x ∈ s
        · simp only [huv, hout, hu, hv, indicator_of_mem hx, hsum, Pi.add_apply]
        · simp only [huv, hout, hu, hv, indicator_of_notMem hx, Pi.add_apply, zero_add]
      map_smul' := fun c u ↦ by
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [(MemLp.indicator hs.nullMeasurableSet (Lp.memLp (c • u))).coeFn_toLp,
          (MemLp.indicator hs.nullMeasurableSet (Lp.memLp u)).coeFn_toLp,
          Lp.coeFn_smul c u, Lp.coeFn_smul c
            ((MemLp.indicator hs.nullMeasurableSet (Lp.memLp u)).toLp _)] with x hcu hu hsmul hout
        by_cases hx : x ∈ s
        · simp only [hcu, hout, hu, indicator_of_mem hx, hsmul, Pi.smul_apply]
        · simp only [hcu, hout, hu, indicator_of_notMem hx, Pi.smul_apply, smul_zero] }
    1 (fun u ↦ by
      change ‖(MemLp.indicator hs.nullMeasurableSet (Lp.memLp u)).toLp _‖ ≤ 1 * ‖u‖
      rw [Lp.norm_toLp, one_mul, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.memLp u).eLpNorm_ne_top
        (eLpNorm_indicator_le u hs.nullMeasurableSet))

/-- The cutoff class has the actual indicator representative almost everywhere. -/
theorem indicatorCLM_coeFn {s : Set α} (hs : MeasurableSet s) (u : Lp E p μ) :
    indicatorCLM 𝕜 hs u =ᵐ[μ] s.indicator u :=
  (MemLp.indicator hs.nullMeasurableSet (Lp.memLp u)).coeFn_toLp

/-- Cutting off to a measurable set cannot increase the Lp norm. -/
theorem norm_indicatorCLM_apply_le {s : Set α} (hs : MeasurableSet s) (u : Lp E p μ) :
    ‖indicatorCLM 𝕜 hs u‖ ≤ ‖u‖ := by
  change ‖(MemLp.indicator hs.nullMeasurableSet (Lp.memLp u)).toLp _‖ ≤ ‖u‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp u).eLpNorm_ne_top
    (eLpNorm_indicator_le u hs.nullMeasurableSet)

/-- Moving a half-line cutoff is strongly continuous at every finite normed
exponent. The endpoint has zero measure, and the original function dominates. -/
theorem continuous_indicatorCLM_Ici (hp : p ≠ ∞)
    (u : Lp E p (volume : Measure ℝ)) :
    Continuous (fun s : ℝ ↦ indicatorCLM 𝕜 (s := Ici s) measurableSet_Ici u) := by
  refine continuous_iff_seqContinuous.mpr ?_
  intro v s hv
  change Tendsto (fun n ↦ (MemLp.indicator measurableSet_Ici.nullMeasurableSet (Lp.memLp u)).toLp
    ((Ici (v n)).indicator u)) atTop
      (𝓝 ((MemLp.indicator measurableSet_Ici.nullMeasurableSet
        (Lp.memLp u)).toLp ((Ici s).indicator u)))
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
  refine tendsto_Lp_of_tendsto_ae_of_ae_norm_le (Fact.out : 1 ≤ p) hp
    (fun _ ↦ (Lp.aestronglyMeasurable u).indicator measurableSet_Ici)
    (MemLp.indicator measurableSet_Ici.nullMeasurableSet (Lp.memLp u)) (Lp.memLp u)
    (fun _ ↦ Eventually.of_forall fun x ↦ norm_indicator_le_norm_self _ _) ?_
  filter_upwards [volume.ae_ne s] with x hx
  rcases lt_or_gt_of_ne hx with hxs | hsx
  · have hs : (Ici s).indicator u x = 0 := indicator_of_notMem (not_le.mpr hxs) _
    rw [hs]
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : E)) atTop (𝓝 0)).congr'
    filter_upwards [hv.eventually (Ioi_mem_nhds hxs)] with n hn
    exact (indicator_of_notMem (not_le.mpr hn) u).symm
  · have hs : (Ici s).indicator u x = u x := indicator_of_mem hsx.le _
    rw [hs]
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ u x) atTop (𝓝 (u x))).congr'
    filter_upwards [hv.eventually (Iio_mem_nhds hsx)] with n hn
    exact (indicator_of_mem hn.le u).symm

/-- A moving half-line cutoff acts jointly continuously in time and the Lp input. -/
theorem continuous_indicatorCLM_Ici_apply (hp : p ≠ ∞) :
    Continuous (fun z : ℝ × Lp E p (volume : Measure ℝ) ↦
      indicatorCLM 𝕜 (s := Ici z.1) measurableSet_Ici z.2) := by
  refine continuous_prod_of_continuous_lipschitzWith' _ 1 ?_
    (continuous_indicatorCLM_Ici hp)
  intro s
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simpa only [_root_.dist_eq_norm, NNReal.coe_one, one_mul, ← map_sub] using
    norm_indicatorCLM_apply_le (𝕜 := 𝕜) (s := Ici s) measurableSet_Ici (u - v)

end MeasureTheory.Lp
