/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.UnifTight

/-!
# Dominated convergence in `Lᵖ`

A form of the Vitali convergence theorem on arbitrary measure spaces: an a.e. strongly
measurable sequence dominated in norm by a single `Lᵖ` function is uniformly integrable and
uniformly tight, so almost-everywhere convergence implies convergence in `Lᵖ`.
-/

@[expose] public section

noncomputable section

open Filter
open scoped MeasureTheory ENNReal Topology

namespace MeasureTheory

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup E]

/-- An a.e. strongly measurable family dominated in norm by a uniformly
integrable family is uniformly integrable. The families may take values in
different normed groups. Measurability is needed because a norm bound alone
does not control the measurability of the dominated function. -/
theorem UnifIntegrable.mono_norm {F ι : Type*} [NormedAddCommGroup F]
    {p : ℝ≥0∞} {f : ι → α → E} {g : ι → α → F}
    (hg : UnifIntegrable g p μ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hfg : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ ‖g i x‖) :
    UnifIntegrable f p μ := by
  rw [unifIntegrable_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hgδ⟩ := hg ε hε
  refine ⟨δ, hδ, fun i s hμs ↦ ?_⟩
  exact (eLpNorm_mono_ae (hf i).restrict
    ((hfg i).filter_mono ae_restrict_le)).trans (hgδ i s hμs)

/-- Domination in norm preserves uniform tightness for an a.e. strongly
measurable family. A measurable set of finite measure is chosen so that the
dominated tails remain measurable. -/
theorem UnifTight.mono_norm {F ι : Type*} [NormedAddCommGroup F]
    {p : ℝ≥0∞} {f : ι → α → E} {g : ι → α → F}
    (hg : UnifTight g p μ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hfg : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ ‖g i x‖) :
    UnifTight f p μ := by
  intro ε hε
  obtain ⟨s, hs, hμs, hgs⟩ := hg.exists_measurableSet_indicator hε.ne'
  refine ⟨s, hμs.ne, fun i ↦ ?_⟩
  refine (eLpNorm_mono_ae ((hf i).indicator hs.compl) ?_).trans (hgs i)
  filter_upwards [hfg i] with x hx
  by_cases hxs : x ∈ sᶜ
  · simpa only [Set.indicator_of_mem hxs] using hx
  · simp only [Set.indicator_of_notMem hxs, norm_zero, le_refl]

/--
Dominated almost-everywhere convergence in `Lᵖ` on an arbitrary measure
space. The dominating function may take values in a different normed group;
in particular, a real-valued bound can control vector-valued functions.
-/
theorem tendsto_Lp_of_tendsto_ae_of_ae_norm_le
    {F : Type*} [NormedAddCommGroup F]
    {p : ℝ≥0∞} {f : ℕ → α → E} {g : α → E} {bound : α → F}
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : MemLp g p μ) (hbound : MemLp bound p μ)
    (hdom : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖bound x‖)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  tendsto_Lp_of_tendsto_ae hp hp_top hf hg
    ((unifIntegrable_const hp hp_top hbound).mono_norm hf hdom)
    ((unifTight_const hp_top hbound).mono_norm hf hdom) hfg

/--
Products converge in `Lᵖ` when the scalar multipliers converge almost
everywhere, both the multipliers and their limit are bounded by one, and the
second factors converge in `Lᵖ`.
-/
theorem tendsto_eLpNorm_mul_of_tendsto_ae_of_tendsto_eLpNorm
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {a : ℕ → α → ℝ} {aLimit : α → ℝ}
    {b : ℕ → α → ℝ} {bLimit : α → ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ)
    (haLimit : AEStronglyMeasurable aLimit μ)
    (hb : ∀ n, MemLp (b n) p μ)
    (hbLimit : MemLp bLimit p μ)
    (haBound : ∀ n, ∀ᵐ x ∂μ, |a n x| ≤ 1)
    (haLimitBound : ∀ᵐ x ∂μ, |aLimit x| ≤ 1)
    (haTendsto :
      ∀ᵐ x ∂μ, Tendsto (fun n ↦ a n x) atTop (𝓝 (aLimit x)))
    (hbTendsto :
      Tendsto (fun n ↦ eLpNorm (b n - bLimit) p μ) atTop (𝓝 0)) :
    Tendsto
      (fun n ↦ eLpNorm
        (fun x ↦ a n x * b n x - aLimit x * bLimit x) p μ)
      atTop (𝓝 0) := by
  let first : ℕ → α → ℝ := fun n x ↦
    a n x * (b n x - bLimit x)
  let second : ℕ → α → ℝ := fun n x ↦
    (a n x - aLimit x) * bLimit x
  have hfirstMeas (n : ℕ) :
      AEStronglyMeasurable (first n) μ :=
    (ha n).mul ((hb n).aestronglyMeasurable.sub
      hbLimit.aestronglyMeasurable)
  have hsecondMeas (n : ℕ) :
      AEStronglyMeasurable (second n) μ :=
    ((ha n).sub haLimit).mul hbLimit.aestronglyMeasurable
  have hfirstBound (n : ℕ) :
      eLpNorm (first n) p μ ≤ eLpNorm (b n - bLimit) p μ := by
    apply eLpNorm_mono_ae (hfirstMeas n)
    filter_upwards [haBound n] with x hx
    simp only [first, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hx
  have hfirstTendsto :
      Tendsto (fun n ↦ eLpNorm (first n) p μ) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hbTendsto
      (fun n ↦ bot_le) (fun n ↦ hfirstBound n)
  have hsecondTendsto :
      Tendsto (fun n ↦ eLpNorm (second n) p μ) atTop (𝓝 0) := by
    have hdom :
        ∀ n, ∀ᵐ x ∂μ, ‖second n x‖ ≤ ‖(2 * bLimit x : ℝ)‖ := by
      intro n
      filter_upwards [haBound n, haLimitBound] with x hax halx
      change |(a n x - aLimit x) * bLimit x| ≤ |2 * bLimit x|
      rw [abs_mul, abs_mul]
      norm_num
      gcongr
      exact (abs_sub _ _).trans (by linarith)
    have hconv :
        ∀ᵐ x ∂μ, Tendsto (fun n ↦ second n x) atTop (𝓝 (0 : ℝ)) := by
      filter_upwards [haTendsto] with x hx
      have hsub :
          Tendsto (fun n ↦ a n x - aLimit x) atTop (𝓝 0) := by
        simpa using hx.sub_const (aLimit x)
      simpa only [zero_mul] using hsub.mul_const (bLimit x)
    simpa only [Pi.sub_apply, sub_zero] using
      (tendsto_Lp_of_tendsto_ae_of_ae_norm_le
        hp hp_top hsecondMeas MemLp.zero
        (hbLimit.const_mul 2) hdom hconv)
  have hsumTendsto :
      Tendsto
        (fun n ↦ eLpNorm (first n + second n) p μ)
        atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      (by simpa using hfirstTendsto.add hsecondTendsto)
      (fun n ↦ bot_le)
      (fun _ ↦ eLpNorm_add_le hp)
  convert hsumTendsto using 1
  funext n
  apply eLpNorm_congr_ae
  filter_upwards [] with x
  simp only [first, second, Pi.add_apply]
  ring

end MeasureTheory
