/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.WeakConvergence
public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Compact uniform traces of bounded weak H¹ families

The real representatives have a common square-root spatial modulus. Weak H¹
convergence gives pointwise convergence by bounded evaluation; equicontinuity
then upgrades it to uniform convergence on every compact set.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- The real representative has the square-root modulus supplied by its weak
derivative, with the graph norm as a common upper bound. -/
theorem dist_realLineRepresentative_le_sqrt (U : W^{1,2}(ℝ^1)) (x y : ℝ) :
    dist (realLineRepresentative U x) (realLineRepresentative U y) ≤
      ‖U‖ * Real.sqrt (dist x y) := by
  have h := (hasWeakTimeDerivativeOn_realLineRepresentative U).enorm_sub_le_eLpNorm_mul_rpow
    (continuous_realLineRepresentative U) (by norm_num : (1 : ℝ≥0∞) < 2) y x
  have hpow : SobolevSpace.morreyExponent 1 2 = (1 / 2 : ℝ) := by
    norm_num [SobolevSpace.morreyExponent]
  rw [hpow] at h
  have hfinite : eLpNorm (realLineCoordinateCLM (singleDerivIndex 1 0) U) 2 volume *
      ENNReal.ofReal |x - y| ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top _) (ENNReal.rpow_ne_top_of_nonneg
      (by norm_num) ENNReal.ofReal_ne_top)
  have hreal := ENNReal.toReal_mono hfinite h
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hreal
  simp only [toReal_enorm, Real.norm_eq_abs, ENNReal.toReal_ofReal (abs_nonneg _),
    ← Real.sqrt_eq_rpow, ← Lp.norm_def] at hreal
  exact hreal.trans (mul_le_mul_of_nonneg_right (norm_realLineCoordinateCLM_le _ U)
    (Real.sqrt_nonneg _))

/-- A bounded family of real H¹ representatives is equicontinuous on the
whole line. No continuity of the family in its parameter is assumed. -/
theorem equicontinuous_realLineRepresentative_of_bound
    {ι : Type*} {u : ι → W^{1,2}(ℝ^1)} {B : ℝ}
    (hbound : ∀ i, ‖u i‖ ≤ B) :
    Equicontinuous (fun i ↦ realLineRepresentative (u i)) := by
  apply Metric.equicontinuous_of_continuity_modulus (fun r ↦ B * Real.sqrt r)
  · simpa only [Real.sqrt_zero, mul_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).const_mul B
  · intro x y i
    exact (dist_realLineRepresentative_le_sqrt (u i) x y).trans
      (mul_le_mul_of_nonneg_right (hbound i) (Real.sqrt_nonneg _))

/-- Bounded weak H¹ convergence implies uniform convergence of the
continuous representatives on each compact set. -/
theorem tendstoUniformlyOn_realLineRepresentative_of_weak
    {ι : Type*} {l : Filter ι} {u : ι → W^{1,2}(ℝ^1)}
    {U : W^{1,2}(ℝ^1)} {B : ℝ}
    (hbound : ∀ i, ‖u i‖ ≤ B)
    (hweak : Tendsto (fun i ↦ toWeakSpace ℝ (W^{1,2}(ℝ^1)) (u i)) l
      (𝓝 (toWeakSpace ℝ (W^{1,2}(ℝ^1)) U)))
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun i ↦ realLineRepresentative (u i))
      (realLineRepresentative U) l K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hequi : Equicontinuous (fun i (x : K) ↦ realLineRepresentative (u i) x) :=
    (equicontinuous_restrict_iff _).mpr
      ((equicontinuous_realLineRepresentative_of_bound hbound).equicontinuousOn K)
  have hpoint : Tendsto (fun i (x : K) ↦ realLineRepresentative (u i) x) l
      (𝓝 (fun x : K ↦ realLineRepresentative U x)) :=
    tendsto_pi_nhds.mpr fun x ↦
      PDE.Analysis.WeakCompactness.tendsto_evaluation hweak (realLineRepresentativeEvalCLM x)
  exact tendstoUniformlyOn_iff_restrict.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp
      ((hequi.tendsto_uniformFun_iff_pi l _).mpr hpoint))

end SobolevSpace.GraphSpace
