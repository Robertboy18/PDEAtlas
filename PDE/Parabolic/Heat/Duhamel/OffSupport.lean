/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Kernel.Regularity
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import PDE.Analysis.Convolution.LocalRegularity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth heat potentials away from the spatial source

For a continuous source on a compact spatial set and a finite time interval,
the retarded heat potential is smooth away from the spatial source. In
particular its regularity crosses the top time of the source interval.
Compactness and separation provide every required integrability statement.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology Interval

namespace HeatEquation

variable {n : ℕ}

/-- A compact heat potential is smooth at every point separated spatially
from its source. The time coordinate may lie anywhere relative to the source
interval, including at its endpoints. -/
theorem contDiffAt_heatPotential_of_spatial_gap
    {K : Set (ℝ^n)} {a b r : ℝ} {R : ℝ^n × ℝ → ℝ}
    (hK : IsCompact K) (hR : ContinuousOn R (K ×ˢ Icc a b))
    {x : ℝ^n} (t : ℝ) (hr : 0 < r)
    (hgap : ∀ y ∈ K, r ≤ dist x y) {m : ℕ∞} :
    ContDiffAt ℝ m (fun p : ℝ^n × ℝ ↦
      ∫ q in K ×ˢ Icc a b,
        R q * fundamentalSolutionHeat (p.1 - q.1) (p.2 - q.2)) (x, t) := by
  have hQ : IsCompact (K ×ˢ Icc a b) := hK.prod isCompact_Icc
  have hRI : LocallyIntegrable R (volume.restrict (K ×ˢ Icc a b)) :=
    (hR.integrableOn_compact hQ).locallyIntegrable
  obtain ⟨M, hM⟩ := hQ.exists_bound_of_continuousOn
    (show ContinuousOn (fun q : ℝ^n × ℝ ↦ dist (x, t) q) (K ×ˢ Icc a b) from
      (continuous_const.dist continuous_id).continuousOn)
  have hsource : ∀ᵐ q ∂volume.restrict (K ×ˢ Icc a b),
      r ≤ dist (x, t) q ∧ dist (x, t) q ≤ M := by
    filter_upwards [ae_restrict_mem hQ.measurableSet] with q hq
    refine ⟨(hgap q.1 hq.1).trans (le_max_left _ _), ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hM q hq
  simpa only [smul_eq_mul, Prod.fst_sub, Prod.snd_sub, Function.uncurry_def] using
    (contDiffAt_integral_smul_sub_of_annulus
      (contDiffOn_fundamentalSolutionHeat (n := n) (m := m)) hRI hr hsource)

/-- The retarded kernel times a continuous source is integrable on a compact
spacetime source set, whenever the spatial evaluation point is outside that set. -/
theorem integrableOn_heatKernel_mul_of_notMem
    {K : Set (ℝ^n)} {a b : ℝ} {R : ℝ^n × ℝ → ℝ}
    (hK : IsCompact K) (hR : ContinuousOn R (K ×ˢ Icc a b))
    {x : ℝ^n} (hx : x ∉ K) (t : ℝ) :
    IntegrableOn (fun q : ℝ^n × ℝ ↦
      R q * fundamentalSolutionHeat (x - q.1) (t - q.2)) (K ×ˢ Icc a b) := by
  apply ContinuousOn.integrableOn_compact (hK.prod isCompact_Icc)
  intro q hq
  have hsp : x - q.1 ≠ 0 := sub_ne_zero.mpr (ne_of_mem_of_not_mem hq.1 hx).symm
  exact (hR q hq).mul
    (((contDiffAt_fundamentalSolutionHeat_of_spatial_ne_zero (m := 0) hsp).continuousAt.comp
      ((continuous_const.sub continuous_fst).prodMk
        (continuous_const.sub continuous_snd)).continuousAt).continuousWithinAt)

/-- Fubini identifies the compact spacetime potential with its iterated
time-space integral. Integrability is derived from compactness and separation. -/
theorem heatPotential_eq_intervalIntegral_of_notMem
    {K : Set (ℝ^n)} {a b : ℝ} {R : ℝ^n × ℝ → ℝ}
    (hab : a ≤ b) (hK : IsCompact K)
    (hR : ContinuousOn R (K ×ˢ Icc a b))
    {x : ℝ^n} (hx : x ∉ K) (t : ℝ) :
    (∫ q in K ×ˢ Icc a b,
      R q * fundamentalSolutionHeat (x - q.1) (t - q.2)) =
      ∫ s in a..b, ∫ y in K,
        fundamentalSolutionHeat (x - y) (t - s) * R (y, s) := by
  have hI := integrableOn_heatKernel_mul_of_notMem hK hR hx t
  have hprod : Integrable (fun q : ℝ^n × ℝ ↦
      R q * fundamentalSolutionHeat (x - q.1) (t - q.2))
      ((volume.restrict K).prod (volume.restrict (Icc a b))) := by
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [integral_prod_symm _ hprod, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]
  congr 1
  funext s
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦ mul_comm _ _

end HeatEquation
