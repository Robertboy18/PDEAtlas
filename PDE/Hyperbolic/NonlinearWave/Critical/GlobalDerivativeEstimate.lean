/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.SpaceTimeContinuity
public import PDE.FDeriv.SpaceTime
public import PDE.Hyperbolic.NonlinearWave.Critical.PersistenceTail
import Mathlib.MeasureTheory.Integral.Bochner.Set
import PDE.Analysis.Calculus.SpaceTime.Support

/-!
# Whole-space derivative bounds from critical tails

For a C¹ field with speed-one support, finite critical mixed norm yields uniform L⁶ bounds for its
first derivatives on a late time interval, conditional on their physical linear estimates. Section
integrability and continuity follow from the field and its support.

This is the absorption argument of step 2 of the proof of Evans, §12.4, Theorem 3, which derives
`sup ‖Du‖_{L⁶} ≤ C` from (17); we apply it on one late interval instead of iterating over the
intervals `[kτ, (k+1)τ]`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 3, step 2 of its proof, equation (17).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common PDE.Analysis
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- For a forward field with speed-one support, finite critical norm absorbs
the differentiated estimate on a late interval. Only C1 interior regularity is used. -/
theorem exists_global_tail_partialDeriv_bound {u : ℝ^4 → ℝ} {T R b K : ℝ} (hb : 0 < b) (hbT : b < T)
    (hu : ContDiffOn ℝ 1 u {p | 0 < p 0 ∧ p 0 < T}) (i : Fin 4)
    (hsupport : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, R + t < ‖x‖ → u (timeSpaceCons t x) = 0) (hK : 0 ≤ K)
    (hcritical : MemLp (fun t ↦ lpNorm (fun x ↦ u (timeSpaceCons t x)) 12 volume) 4
      (volume.restrict (Ico b T)))
    (hlinear : ∀ s ∈ Ioo b T, ∃ A : ℝ, ∀ r ∈ Ico s T, lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x))
      6 volume ≤ A + K * ∫ q in Icc s r,
      lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 * (∂[i] u) (timeSpaceCons q x)) 2 volume) :
    ∃ s ∈ Ioo b T, ∃ M : ℝ, ∀ r ∈ Ico s T,
      lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6 volume ≤ M := by
  classical
  let D : Set (ℝ^4) := {p | 0 < p 0 ∧ p 0 < T}
  have hopen : IsOpen D := (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hv : ContinuousOn (∂[i] u) D :=
    (hu.continuousOn_fderiv_of_isOpen hopen (by norm_num)).clm_apply continuousOn_const
  let S : TopologicalSpace.Compacts (ℝ^3) := ⟨Metric.closedBall 0 (R + T), isCompact_closedBall _ _⟩
  have hS {x : ℝ^3} (hx : x ∉ S) : R + T < ‖x‖ := by
    change x ∉ Metric.closedBall 0 (R + T) at hx
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have hus : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, x ∉ S → u (timeSpaceCons t x) = 0 :=
    fun t ht x hx ↦ hsupport t ht x (by linarith [hS hx, ht.2])
  have hvs : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, x ∉ S → (∂[i] u) (timeSpaceCons t x) = 0 :=
    fun t ht x hx ↦ partialDeriv_eq_zero_of_forward_support hsupport ht i (hS hx)
  let U : ℝ × ℝ^3 → ℝ := fun q ↦ D.indicator u (timeSpaceCons q.1 q.2)
  let V : ℝ × ℝ^3 → ℝ := fun q ↦ D.indicator (∂[i] u) (timeSpaceCons q.1 q.2)
  have hc : Continuous (fun q : ℝ × ℝ^3 ↦ timeSpaceCons q.1 q.2) :=
    (timeSpaceContinuousLinearEquiv 3).symm.continuous
  have hmeas {w : ℝ^4 → ℝ} (hw : ContinuousOn w D) :
      Measurable (fun q : ℝ × ℝ^3 ↦ D.indicator w (timeSpaceCons q.1 q.2)) := by
    have hm : Measurable (D.indicator w) := by
      simpa only [piecewise_eq_indicator] using
        hw.measurable_piecewise continuous_zero.continuousOn hopen.measurableSet
    exact hm.comp hc.measurable
  have he {w : ℝ^4 → ℝ} {t : ℝ} (ht : t ∈ Ioo 0 T) :
      (fun x ↦ D.indicator w (timeSpaceCons t x)) = fun x ↦ w (timeSpaceCons t x) :=
    funext fun x ↦ indicator_of_mem (by simpa [D] using ht) w
  have hm {w : ℝ^4 → ℝ} (hw : ContinuousOn w D)
      (hws : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, x ∉ S → w (timeSpaceCons t x) = 0)
      {t : ℝ} (ht : t ∈ Ioo 0 T) (p : ℝ≥0∞) :
      MemLp (fun x ↦ D.indicator w (timeSpaceCons t x)) p volume := by
    rw [he ht]
    apply (hw.comp_continuous (hc.comp (continuous_const.prodMk continuous_id))
      (fun x ↦ by simpa [D] using ht)).memLp_of_hasCompactSupport
    exact S.isCompact.of_isClosed_subset (isClosed_tsupport _) (closure_minimal
      (fun x hx ↦ by_contra fun hnot ↦ hx (hws t ht x hnot)) S.isCompact.isClosed)
  have hcrit : MemLp (fun r ↦ lpNorm (fun x ↦ U (r, x)) 12 volume) 4
      (volume.restrict (Ico b T)) := by
    apply hcritical.ae_eq
    filter_upwards [ae_restrict_mem measurableSet_Ico] with r hr
    dsimp only [U]
    rw [he ⟨hb.trans_le hr.1, hr.2⟩]
  have : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨s, hs, habs⟩ := exists_tail_lpNorm_six_bound hbT (hmeas hu.continuousOn)
    (hmeas hv) hK (fun r hr ↦ hm hu.continuousOn hus ⟨hb.trans_le hr.1, hr.2⟩ 12)
    (fun r hr ↦ hm hv hvs ⟨hb.trans_le hr.1, hr.2⟩ 6)
    (fun s hs t ht ↦ (PDE.Analysis.continuousOn_lpNorm_of_common_spatial_support
      hv S hvs (hb.trans_le hs.1) ht.2).congr (fun r hr ↦ by
        dsimp only [V]
        rw [he ⟨(hb.trans_le hs.1).trans_le hr.1, hr.2.trans_lt ht.2⟩])) hcrit
  obtain ⟨A, hA⟩ := hlinear s hs
  refine ⟨s, hs, 2 * A, ?_⟩
  have hbnd := habs A (fun r hr ↦ ?_)
  · intro r hr
    simpa only [V, he ⟨(hb.trans hs.1).trans_le hr.1, hr.2⟩] using hbnd r hr
  · dsimp only [V]
    rw [he ⟨(hb.trans hs.1).trans_le hr.1, hr.2⟩]
    convert hA r hr using 1
    congr 2
    apply setIntegral_congr_fun measurableSet_Icc
    intro q hq
    dsimp only [U, V]
    congr 1
    funext x
    have hq0 : q ∈ Ioo 0 T := ⟨(hb.trans hs.1).trans_le hq.1, hq.2.trans_lt hr.2⟩
    rw [congrFun (he (w := u) hq0) x, congrFun (he (w := ∂[i] u) hq0) x]

end WaveEquation.Critical
