/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import PDE.Analysis.Convolution.ParameterDerivative

/-!
# Approximation by spatial convolution with parameters

Normalized bump functions approximate a jointly continuous family locally
uniformly, including its parameter dependence. For a C¹ family with common
compact spatial support, the same convergence holds for every directional
derivative. The proofs combine Mathlib's approximate identity and parameter
convolution theorems.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory
open scoped Topology Convolution

namespace ContDiffBump

variable {P G E ι : Type*} [TopologicalSpace P]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure G} [μ.IsAddHaarMeasure]

/-- A normalized spatial convolution converges locally uniformly with all
jointly continuous parameters on an arbitrary parameter set. Compact spatial
support of the field is not needed. -/
theorem tendstoLocallyUniformlyOn_convolution_parameter
    {u : P × G → E} {S : Set P}
    (hu : ContinuousOn u (S ×ˢ univ))
    {φ : ι → ContDiffBump (0 : G)} {l : Filter ι}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) :
    TendstoLocallyUniformlyOn
      (fun i p ↦ ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
        (fun y ↦ u (p.1, y))) p.2)
      u l (S ×ˢ univ) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro p hp
  have hc := hu.continuousWithinAt hp
  have hparam : Tendsto (fun j : ι × (P × G) ↦ j.2.1)
      (l ×ˢ 𝓝[S ×ˢ univ] p) (𝓝 p.1) :=
    continuous_fst.continuousWithinAt.tendsto.comp tendsto_snd
  have hx : Tendsto (fun j : ι × (P × G) ↦ j.2.2)
      (l ×ˢ 𝓝[S ×ˢ univ] p) (𝓝 p.2) :=
    continuous_snd.continuousWithinAt.tendsto.comp tendsto_snd
  have hmeas : ∀ᶠ j : ι × (P × G) in l ×ˢ 𝓝[S ×ˢ univ] p,
      AEStronglyMeasurable (fun y ↦ u (j.2.1, y)) μ := by
    filter_upwards [tendsto_snd.eventually
      (self_mem_nhdsWithin : ∀ᶠ q in 𝓝[S ×ˢ univ] p, q ∈ S ×ˢ univ)] with j hj
    exact (hu.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y ↦ ⟨hj.1, mem_univ y⟩)).aestronglyMeasurable
  have hfield : Tendsto
      (fun q : (ι × (P × G)) × G ↦ u (q.1.2.1, q.2))
      ((l ×ˢ 𝓝[S ×ˢ univ] p) ×ˢ 𝓝 p.2) (𝓝 (u p)) :=
    hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨
      (hparam.comp tendsto_fst).prodMk_nhds tendsto_snd, by
      filter_upwards [(tendsto_snd.comp tendsto_fst).eventually
        (self_mem_nhdsWithin : ∀ᶠ q in 𝓝[S ×ˢ univ] p, q ∈ S ×ˢ univ)] with q hq
      exact ⟨hq.1, mem_univ _⟩⟩)
  have hconv := convolution_tendsto_right
    (μ := μ) (φ := fun j : ι × (P × G) ↦ φ j.1)
    (g := fun j y ↦ u (j.2.1, y)) (k := fun j ↦ j.2.2)
    (hφ.comp tendsto_fst) hmeas hfield hx
  exact ((hc.tendsto.comp tendsto_snd).prodMk_nhds hconv).mono_right
    (nhds_le_uniformity (u p))

/-- Spatial smoothing approximates every directional derivative locally
uniformly in the parameter and spatial variables. The family needs C¹
regularity and a common compact spatial support. -/
theorem tendstoLocallyUniformlyOn_fderiv_convolution_parameter_apply
    {P G E ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    {u : P × G → E} {S : Set P} {K : Set G}
    (hS : IsOpen S) (hK : IsCompact K)
    (hu : ContDiffOn ℝ 1 u (S ×ˢ univ))
    (hs : ∀ p ∈ S, ∀ x ∉ K, u (p, x) = 0)
    {φ : ι → ContDiffBump (0 : G)} {l : Filter ι}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) (v : P × G) :
    TendstoLocallyUniformlyOn
      (fun i p ↦ fderiv ℝ (fun q : P × G ↦
        ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
          (fun y ↦ u (q.1, y))) q.2) p v)
      (fun p ↦ fderiv ℝ u p v) l (S ×ˢ univ) := by
  have hDu : ContinuousOn (fun p ↦ fderiv ℝ u p v) (S ×ˢ univ) :=
    (hu.continuousOn_fderiv_of_isOpen (hS.prod isOpen_univ) le_rfl).clm_apply
      continuousOn_const
  refine (tendstoLocallyUniformlyOn_convolution_parameter (μ := μ) hDu hφ).congr ?_
  intro i p hp
  have he := fderiv_convolution_left_with_param_apply (μ := μ)
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hS hK hu hs
    ((φ i).continuous_normed (μ := μ)).locallyIntegrable hp.1 v
  simpa only [convolution_flip] using he.symm

end ContDiffBump
