/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.SpaceTime
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import PDE.Analysis.MeasureTheory.Integral.CollarEstimate
import PDE.Analysis.MeasureTheory.Lp.CompactSupportContinuity
import PDE.FDeriv.SpaceTime

/-!
# Bounds and convergence of `L²` pairings and of compactly supported time slices

The integral of a pointwise inner product, or of a product of norms, of two `L²` functions is
bounded by the product of their `L²` norms. If two families converge in `L²`, their pointwise
inner products have convergent integrals. The time slices of a continuous compactly supported
function on spacetime have uniformly bounded `L²` norms and converge in `L²` as the time
converges.
-/

@[expose] public section

namespace PDE.Analysis

open EuclideanSpace MeasureTheory Filter PDE.Common
open scoped Topology ENNReal

set_option linter.missingDocs true

section Bounds

variable {n : ℕ}

/-- The integral of the squared norm of an `L²` function is the square of its `L²` norm. -/
theorem integral_norm_sq_eq_eLpNorm_toReal_sq {X E : Type*} [MeasurableSpace X]
    {μ : Measure X} [NormedAddCommGroup E] {f : X → E} (hf : MemLp f 2 μ) :
    ∫ x, ‖f x‖ ^ 2 ∂μ = (eLpNorm f 2 μ).toReal ^ 2 := by
  rw [← Lp.norm_toLp f hf, Lp.norm_sq_eq_integral_norm_sq]
  exact integral_congr_ae (hf.coeFn_toLp.fun_comp fun z ↦ ‖z‖ ^ 2).symm

/-- The integral of the pointwise inner product of two `L²` functions is bounded by the product
of their `L²` norms; this is `sq_integral_inner_le_integral_norm_sq_mul` with the squared
norms written as `L²` norms. -/
theorem abs_integral_inner_le_eLpNorm_mul {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f g : X → E}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, inner ℝ (f x) (g x) ∂μ| ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have h := sq_integral_inner_le_integral_norm_sq_mul hf hg
  rw [integral_norm_sq_eq_eLpNorm_toReal_sq hf, integral_norm_sq_eq_eLpNorm_toReal_sq hg,
    ← mul_pow, ← sq_abs] at h
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).1 h

/-- A continuous compactly supported spacetime field has square-integrable fixed-time slices
whose `L²` norms are bounded uniformly in time. -/
theorem exists_eLpNorm_slice_le {E : Type*} [NormedAddCommGroup E] {F : ℝ^(n + 1) → E}
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, MemLp (fun x ↦ F (timeSpaceCons t x)) 2 volume ∧
      (eLpNorm (fun x ↦ F (timeSpaceCons t x)) 2 volume).toReal ≤ M := by
  obtain ⟨C, hC⟩ := hF.bounded_above_of_compact_support hFc
  set K : Set (ℝ^n) := spatialPartCLM n '' tsupport F
  have hK : IsCompact K := hFc.image (spatialPartCLM n).continuous
  have hg : MemLp (K.indicator fun _ ↦ C) 2 (volume : Measure (ℝ^n)) :=
    memLp_indicator_const 2 hK.measurableSet.nullMeasurableSet C (Or.inr hK.measure_lt_top.ne)
  have hle : ∀ t x, ‖F (timeSpaceCons t x)‖ ≤ K.indicator (fun _ ↦ C) x := by
    intro t x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      exact hC _
    · rw [Set.indicator_of_notMem hx]
      have hxF : timeSpaceCons t x ∉ tsupport F :=
        fun h ↦ hx ⟨_, h, spatialPartCLM_timeSpaceCons t x⟩
      simp [image_eq_zero_of_notMem_tsupport hxF]
  have hmeas : ∀ t, AEStronglyMeasurable (fun x : ℝ^n ↦ F (timeSpaceCons t x)) volume :=
    fun t ↦ (hF.comp (contDiff_timeSpaceCons_spatial n t (m := 0)).continuous).aestronglyMeasurable
  refine ⟨(eLpNorm (K.indicator fun _ ↦ C) 2 volume).toReal, ENNReal.toReal_nonneg,
    fun t ↦ ⟨?_, ?_⟩⟩
  · exact (eLpNorm_mono_real (hmeas t) (hle t)).trans_lt hg
  · exact ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_mono_real (hmeas t) (hle t))

/-- The Cauchy–Schwarz inequality for the norms of two square-integrable functions. -/
theorem integral_norm_mul_norm_le_eLpNorm_mul {α E F : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : α → F}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
    (f := fun x ↦ ‖f x‖) (g := fun x ↦ ‖g x‖) (by simpa using hf.norm) (by simpa using hg.norm)
  simp only [norm_norm] at h
  refine h.trans_eq ?_
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  norm_num

end Bounds

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Classes in `Lᵖ` converge when they eventually represent functions converging in `Lᵖ` to a
representative of the limit class. -/
private theorem tendsto_Lp_of_ae_eq {α F ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {l : Filter ι} {f : ι → α → F}
    {g : α → F} {V : ι → Lp F p μ} {W : Lp F p μ} (hV : ∀ᶠ k in l, V k =ᵐ[μ] f k)
    (hW : W =ᵐ[μ] g) (hlim : Tendsto (fun k ↦ eLpNorm (f k - g) p μ) l (𝓝 0)) :
    Tendsto V l (𝓝 W) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine hlim.congr' ?_
  filter_upwards [hV] with k hk
  exact (eLpNorm_congr_ae (hk.sub hW)).symm

/-- Integrals of inner products are jointly continuous for `L²` convergence. -/
theorem tendsto_integral_inner_of_tendsto_eLpNorm {ι : Type*} {l : Filter ι}
    {v ψ : ι → ℝ^n → E} {w ψ₀ : ℝ^n → E}
    (hv : ∀ᶠ k in l, MemLp (v k) 2 volume) (hw : MemLp w 2 volume)
    (hψ : ∀ᶠ k in l, MemLp (ψ k) 2 volume) (hψ₀ : MemLp ψ₀ 2 volume)
    (hvlim : Tendsto (fun k ↦ eLpNorm (v k - w) 2 volume) l (𝓝 0))
    (hψlim : Tendsto (fun k ↦ eLpNorm (ψ k - ψ₀) 2 volume) l (𝓝 0)) :
    Tendsto (fun k ↦ ∫ x, inner ℝ (v k x) (ψ k x)) l (𝓝 (∫ x, inner ℝ (w x) (ψ₀ x))) := by
  classical
  let V : ι → Lp E 2 (volume : Measure (ℝ^n)) := fun k ↦
    if h : MemLp (v k) 2 volume then h.toLp (v k) else 0
  let Ψ : ι → Lp E 2 (volume : Measure (ℝ^n)) := fun k ↦
    if h : MemLp (ψ k) 2 volume then h.toLp (ψ k) else 0
  have hV : ∀ᶠ k in l, V k =ᵐ[volume] v k := by
    filter_upwards [hv] with k hk
    simpa only [V, dite_eq_left hk] using hk.coeFn_toLp
  have hΨ : ∀ᶠ k in l, Ψ k =ᵐ[volume] ψ k := by
    filter_upwards [hψ] with k hk
    simpa only [Ψ, dite_eq_left hk] using hk.coeFn_toLp
  have hlim := (tendsto_Lp_of_ae_eq hV hw.coeFn_toLp hvlim).inner (𝕜 := ℝ)
    (tendsto_Lp_of_ae_eq hΨ hψ₀.coeFn_toLp hψlim)
  have hlim₀ : inner ℝ (hw.toLp w) (hψ₀.toLp ψ₀) = ∫ x, inner ℝ (w x) (ψ₀ x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp, hψ₀.coeFn_toLp] with x h₁ h₂
    rw [h₁, h₂]
  rw [hlim₀] at hlim
  refine hlim.congr' ?_
  filter_upwards [hV, hΨ] with k hVk hΨk
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hVk, hΨk] with x h₁ h₂
  rw [h₁, h₂]

/-- The time slices of a continuous compactly supported spacetime function converge in `L²`. -/
theorem tendsto_eLpNorm_timeSlice_sub {φ : ℝ^(n + 1) → E} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (τ₀ : ℝ) :
    Tendsto (fun τ ↦ eLpNorm (fun x ↦ φ (timeSpaceCons τ x) - φ (timeSpaceCons τ₀ x)) 2 volume)
      (𝓝 τ₀) (𝓝 0) := by
  let K : TopologicalSpace.Compacts (ℝ^n) :=
    ⟨spatialPartCLM n '' tsupport φ, hc.isCompact.image (spatialPartCLM n).continuous⟩
  let f : ℝ → ℝ^n → E := fun τ x ↦ φ (timeSpaceCons τ x) - φ (timeSpaceCons τ₀ x)
  have hcons : Continuous fun p : ℝ × ℝ^n ↦ timeSpaceCons p.1 p.2 :=
    (timeSpaceContinuousLinearEquiv n).symm.continuous
  have hf : Continuous f.uncurry :=
    (hφ.comp hcons).sub (hφ.comp (hcons.comp (continuous_const.prodMk continuous_snd)))
  have hzero : ∀ τ x, x ∉ (K : Set (ℝ^n)) → φ (timeSpaceCons τ x) = 0 := by
    intro τ x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hx ⟨timeSpaceCons τ x, hmem, spatialPartCLM_timeSpaceCons τ x⟩
  have hsupp : ∀ τ x, x ∉ (K : Set (ℝ^n)) → f τ x = 0 := by
    intro τ x hx
    simp only [f, hzero τ x hx, hzero τ₀ x hx, sub_self]
  have hmem : ∀ τ, MemLp (f τ) 2 volume := by
    intro τ
    exact (hf.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
      (HasCompactSupport.intro K.isCompact (hsupp τ))
  have hcont := continuous_lpNorm_of_common_compact_support (p := 2)
    (μ := (volume : Measure (ℝ^n))) K hf hsupp
  have hlim := ENNReal.tendsto_ofReal (hcont.tendsto τ₀)
  have hτ₀ : f τ₀ = fun _ ↦ 0 := by
    funext x
    exact sub_self _
  rw [hτ₀, lpNorm_fun_zero, ENNReal.ofReal_zero] at hlim
  refine hlim.congr fun τ ↦ ?_
  exact ofReal_lpNorm (hmem τ)

end PDE.Analysis
