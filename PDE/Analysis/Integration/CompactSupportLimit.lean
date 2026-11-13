/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Uniform limits in compactly supported integral pairings

Uniform convergence with eventual support in one compact set permits testing against
a locally integrable coefficient. The coefficient only needs to be integrable on that set.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace MeasureTheory

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]

/-- Uniform convergence with eventual support in one compact set passes through pairing
with an integrable coefficient. The coefficient only needs to be integrable on that set. -/
theorem tendsto_integral_smul_of_uniformOn_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set X} (hK : IsCompact K) {f : X → E} {ψ : X → ℝ} {a : ι → X → ℝ}
    (hf : IntegrableOn f K μ) (hψ : Continuous ψ) (ha : ∀ i, Continuous (a i))
    (hψK : ∀ x ∉ K, ψ x = 0) (haK : ∀ᶠ i in l, ∀ x ∉ K, a i x = 0)
    (hconv : TendstoUniformlyOn a ψ l K) :
    Tendsto (fun i ↦ ∫ x, a i x • f x ∂μ) l (𝓝 (∫ x, ψ x • f x ∂μ)) := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image hψ.norm.continuousOn
  have hbound : ∀ᶠ i in l, ∀ x ∈ K, ‖a i x‖ ≤ C + 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv 1 zero_lt_one] with i hi x hx
    calc
      ‖a i x‖ ≤ ‖ψ x‖ + ‖ψ x - a i x‖ := norm_le_norm_add_norm_sub _ _
      _ ≤ C + 1 := add_le_add (hC (mem_image_of_mem _ hx))
        (by simpa only [dist_eq_norm] using (hi x hx).le)
  have hlim : Tendsto (fun i ↦ ∫ x in K, a i x • f x ∂μ) l
      (𝓝 (∫ x in K, ψ x • f x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ (C + 1) * ‖f x‖)
    · exact Eventually.of_forall fun i ↦ (ha i).aestronglyMeasurable.smul hf.aestronglyMeasurable
    · filter_upwards [hbound] with i hi
      filter_upwards [ae_restrict_mem₀ hK.measurableSet.nullMeasurableSet] with x hx
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hi x hx) (norm_nonneg _)
    · exact hf.norm.const_mul _
    · filter_upwards [ae_restrict_mem₀ hK.measurableSet.nullMeasurableSet] with x hx
      exact (hconv.tendsto_at hx).smul_const (f x)
  have hψeq : (∫ x in K, ψ x • f x ∂μ) = ∫ x, ψ x • f x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by rw [hψK x hx, zero_smul]
  rw [hψeq] at hlim
  apply hlim.congr'
  filter_upwards [haK] with i hi
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
    rw [hi x hx, zero_smul]

omit [TopologicalSpace X] [T2Space X] [BorelSpace X] [l.IsCountablyGenerated] in
/-- A bounded compactly supported weight sends convergence to zero in local L¹
to convergence of its vector-valued integral. The weights may vary with the index. -/
theorem tendsto_integral_smul_zero_of_tendsto_integral_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ι → X → E} {a : ι → X → ℝ} {K : Set X} {C : ℝ}
    (hf : ∀ᶠ i in l, IntegrableOn (f i) K μ)
    (haK : ∀ i, ∀ x ∉ K, a i x = 0)
    (hbound : ∀ᶠ i in l, ∀ x, ‖a i x‖ ≤ C)
    (hlim : Tendsto (fun i ↦ ∫ x in K, ‖f i x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, a i x • f i x ∂μ) l (𝓝 0) := by
  have hzero : Tendsto (fun i ↦ C * ∫ x in K, ‖f i x‖ ∂μ) l (𝓝 0) := by
    simpa using hlim.const_mul C
  apply squeeze_zero_norm' ?_ hzero
  filter_upwards [hf, hbound] with i hi hb
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := K) (fun x hx ↦ by rw [haK i x hx, zero_smul])]
  calc
    ‖∫ x in K, a i x • f i x ∂μ‖ ≤ ∫ x in K, C * ‖f i x‖ ∂μ := by
      apply norm_integral_le_of_norm_le (hi.norm.const_mul C)
      filter_upwards with x
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
    _ = C * ∫ x in K, ‖f i x‖ ∂μ := integral_const_mul _ _

omit [l.IsCountablyGenerated] in
/-- Local L¹ convergence of vector fields passes through every continuous
compactly supported scalar test. -/
theorem tendsto_integral_smul_of_locallyL1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ι → X → E} {g : X → E}
    (hf : ∀ᶠ i in l, LocallyIntegrable (f i) μ) (hg : LocallyIntegrable g μ)
    (hlim : ∀ K : Set X, IsCompact K →
      Tendsto (fun i ↦ ∫ x in K, ‖f i x - g x‖ ∂μ) l (𝓝 0))
    {ψ : X → ℝ} (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    Tendsto (fun i ↦ ∫ x, ψ x • f i x ∂μ) l (𝓝 (∫ x, ψ x • g x ∂μ)) := by
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hs
  have hzero : Tendsto (fun i ↦ ∫ x, ψ x • (f i x - g x) ∂μ) l (𝓝 0) :=
    tendsto_integral_smul_zero_of_tendsto_integral_norm
      (hf.mono fun _ hi ↦ (hi.sub hg).integrableOn_isCompact hs)
      (fun _ _ hx ↦ image_eq_zero_of_notMem_tsupport hx)
      (Eventually.of_forall fun _ x ↦ hC x) (hlim _ hs)
  have hadd := hzero.add (tendsto_const_nhds (x := ∫ x, ψ x • g x ∂μ))
  simp only [zero_add] at hadd
  apply hadd.congr'
  filter_upwards [hf] with i hi
  have hsub : Integrable (fun x ↦ ψ x • (f i x - g x)) μ :=
    (hi.sub hg).integrable_smul_left_of_hasCompactSupport hψ hs
  rw [← integral_add hsub
    (hg.integrable_smul_left_of_hasCompactSupport hψ hs)]
  simp only [← smul_add, sub_add_cancel]

end MeasureTheory
