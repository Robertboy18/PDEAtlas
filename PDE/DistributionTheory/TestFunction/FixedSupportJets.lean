/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.CommonSupportConvergence
public import PDE.FDeriv.PartialDeriv.Norm
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions

/-!
# Fixed-support smooth jets in weighted Lᵖ

Convergence in the fixed-support smooth topology controls all coordinate derivatives
uniformly. Every finite Lᵖ norm then converges for measures finite on the common compact,
including locally integrable singular weights.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory TopologicalSpace SobolevSpace
open scoped Distributions ENNReal Topology

namespace ContDiffMapSupportedIn

variable {n : ℕ} {K : Compacts (ℝ^n)}

/-- Every coordinate derivative converges uniformly when smooth functions converge in
Mathlib's fixed-support test topology. -/
theorem tendstoUniformly_iteratedPartialDeriv
    {ι : Type*} {l : Filter ι} {f : ι → 𝓓_{K}(ℝ^n, ℝ)} {g : 𝓓_{K}(ℝ^n, ℝ)}
    (h : Tendsto f l (𝓝 g)) (indices : List (Fin n)) :
    TendstoUniformly (fun j ↦ iteratedPartialDeriv indices (f j))
      (iteratedPartialDeriv indices g) l := by
  have hfull := (structureMapCLM ℝ ⊤ indices.length).continuous.tendsto g |>.comp h
  have hfull' : TendstoUniformly (fun j ↦ iteratedFDeriv ℝ indices.length (f j))
      (iteratedFDeriv ℝ indices.length g) l := by
    simpa only [Function.comp_def, structureMapCLM_top_apply] using
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hfull
  rw [Metric.tendstoUniformly_iff] at hfull' ⊢
  intro ε hε
  filter_upwards [hfull' ε hε] with j hj x
  have hf : ContDiff ℝ indices.length (f j) := (f j).contDiff.of_le (by simp)
  have hg : ContDiff ℝ indices.length g := g.contDiff.of_le (by simp)
  have hb := PDE.norm_iteratedPartialDeriv_le_norm_iteratedFDeriv indices
    (x := x) (hg.sub hf).contDiffAt
  change ‖iteratedPartialDeriv indices ((g : ℝ^n → ℝ) - (f j : ℝ^n → ℝ)) x‖ ≤
    ‖iteratedFDeriv ℝ indices.length ((g : ℝ^n → ℝ) - (f j : ℝ^n → ℝ)) x‖ at hb
  rw [congrFun (PDE.iteratedPartialDeriv_sub_of_contDiff indices hg hf) x,
    congrFun (iteratedFDeriv_sub hg hf) x] at hb
  exact hb.trans_lt (by simpa only [dist_eq_norm, Pi.sub_apply] using hj x)

/-- Smooth coordinate jets are integrable to every power for measures finite on compacts. -/
theorem memLp_iteratedPartialDeriv
    (μ : Measure (ℝ^n)) [IsFiniteMeasureOnCompacts μ]
    (p : ℝ≥0∞) (indices : List (Fin n)) (f : 𝓓_{K}(ℝ^n, ℝ)) :
    MemLp (iteratedPartialDeriv indices f) p μ :=
  (PDE.contDiff_top_iteratedPartialDeriv f.contDiff indices).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_iteratedPartialDeriv f.hasCompactSupport indices)

/-- The coordinate jet, as an Lᵖ class, depends continuously on a smooth function
in the fixed-support topology. No pointwise upper bound on a measure density is needed. -/
theorem continuous_iteratedPartialDeriv_toLp
    (μ : Measure (ℝ^n)) [IsFiniteMeasureOnCompacts μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (indices : List (Fin n)) :
    Continuous (fun f : 𝓓_{K}(ℝ^n, ℝ) ↦
      (memLp_iteratedPartialDeriv μ p indices f).toLp (iteratedPartialDeriv indices f)) := by
  rw [continuous_iff_continuousAt]
  intro f
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _
    (fun g ↦ memLp_iteratedPartialDeriv μ p indices g) _
    (memLp_iteratedPartialDeriv μ p indices f)).mpr
  have hsupp (g : 𝓓_{K}(ℝ^n, ℝ)) :
      Function.support (iteratedPartialDeriv indices g) ⊆ (K : Set (ℝ^n)) :=
    (subset_tsupport _).trans
      ((tsupport_iteratedPartialDeriv_subset_tsupport indices g).trans g.tsupport_subset)
  exact tendsto_eLpNorm_sub_of_tendstoUniformlyOn hp K.isCompact.measurableSet.nullMeasurableSet
    K.isCompact.measure_ne_top
    (Eventually.of_forall fun g ↦
      (memLp_iteratedPartialDeriv μ p indices g).aestronglyMeasurable.sub
        (memLp_iteratedPartialDeriv μ p indices f).aestronglyMeasurable)
    (Eventually.of_forall hsupp) (hsupp f)
    (tendstoUniformly_iteratedPartialDeriv tendsto_id indices).tendstoUniformlyOn

end ContDiffMapSupportedIn
