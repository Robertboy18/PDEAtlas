/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integral limits of continuous functions of bounded states

Continuous functions of an essentially bounded measurable state in a proper normed
space are locally integrable. Almost everywhere convergence of uniformly bounded
states passes through continuous composition and pairing with an integrable test
weight. A separate result treats locally uniform convergence of scalar compositions.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A continuous function of an essentially bounded state is locally integrable
when closed balls in the state space are compact. -/
theorem locallyIntegrable_comp_of_ae_bound [TopologicalSpace X] [IsLocallyFiniteMeasure μ]
    {E F : Type*} [NormedAddCommGroup E] [ProperSpace E] [NormedAddCommGroup F]
    {u : X → E} (hu : AEStronglyMeasurable u μ) {M : ℝ}
    (hM : ∀ᵐ x ∂μ, ‖u x‖ ≤ M) {f : E → F} (hf : Continuous f) :
    LocallyIntegrable (fun x ↦ f (u x)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) M).exists_bound_of_continuousOn
    hf.continuousOn
  apply (locallyIntegrable_const C).mono (hf.comp_aestronglyMeasurable hu)
  filter_upwards [hM] with x hx
  exact (hC _ (by simpa using hx)).trans (le_abs_self C)

/-- An almost everywhere limit along a countably generated filter inherits
measurability and a common essential norm bound. A countable cofinal sample
makes the exceptional sets simultaneous; the original limit is retained. -/
theorem aestronglyMeasurable_and_ae_norm_le_of_tendsto
    {ι E : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot]
    [NormedAddCommGroup E] {u : ι → X → E} {v : X → E} {M : ℝ}
    (hu : ∀ᶠ i in l, AEStronglyMeasurable (u i) μ)
    (hM : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖u i x‖ ≤ M)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ u i x) l (𝓝 (v x))) :
    AEStronglyMeasurable v μ ∧ ∀ᵐ x ∂μ, ‖v x‖ ≤ M := by
  obtain ⟨a, ha⟩ := l.exists_seq_tendsto
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ha.eventually (hu.and hM))
  let b : ℕ → ι := fun k ↦ a (k + N)
  have hb : Tendsto b atTop l := ha.comp (tendsto_add_atTop_nat N)
  have hbm (k : ℕ) : AEStronglyMeasurable (u (b k)) μ := (hN _ (by omega)).1
  have hbM : ∀ᵐ x ∂μ, ∀ k, ‖u (b k) x‖ ≤ M :=
    ae_all_iff.mpr fun k ↦ (hN _ (by omega)).2
  have hblim : ∀ᵐ x ∂μ, Tendsto (fun k ↦ u (b k) x) atTop (𝓝 (v x)) :=
    hlim.mono fun _ hx ↦ hx.comp hb
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop hbm hblim, ?_⟩
  filter_upwards [hbM, hblim] with x hx hxl
  exact le_of_tendsto hxl.norm (Eventually.of_forall hx)

/-- Almost everywhere convergence of states with a common essential bound
passes through continuous composition and any integrable scalar weight.
Only the state space, not the codomain of the composition, needs compact balls. -/
theorem tendsto_integral_smul_comp_of_ae_bound
    {ι E F : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ι → X → E} {v : X → E} {M : ℝ}
    (hu : ∀ᶠ i in l, AEStronglyMeasurable (u i) μ)
    (hM : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖u i x‖ ≤ M)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ u i x) l (𝓝 (v x)))
    {f : E → F} (hf : Continuous f) {ψ : X → ℝ} (hψ : Integrable ψ μ) :
    Tendsto (fun i ↦ ∫ x, ψ x • f (u i x) ∂μ) l
      (𝓝 (∫ x, ψ x • f (v x) ∂μ)) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) M).exists_bound_of_continuousOn
    hf.continuousOn
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖ψ x‖ * C)
  · filter_upwards [hu] with i hi
    exact hψ.aestronglyMeasurable.smul (hf.comp_aestronglyMeasurable hi)
  · filter_upwards [hM] with i hi
    filter_upwards [hi] with x hx
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC _ (by simpa using hx)) (norm_nonneg _)
  · exact hψ.norm.mul_const C
  · filter_upwards [hlim] with x hx
    exact tendsto_const_nhds.smul ((hf.tendsto (v x)).comp hx)

/-- Locally uniform convergence on the bounded state range suffices for convergence
after multiplication by any integrable real weight. -/
theorem tendsto_integral_comp_mul_of_ae_bound
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {u : X → ℝ} (hu : AEStronglyMeasurable u μ) {M : ℝ}
    (hM : ∀ᵐ x ∂μ, ‖u x‖ ≤ M) {f : ℝ → ℝ} {F : ι → ℝ → ℝ}
    (hf : Continuous f) (hF : ∀ i, Continuous (F i))
    (hconv : TendstoLocallyUniformly F f l)
    {ψ : X → ℝ} (hψ : Integrable ψ μ) :
    Tendsto (fun i ↦ ∫ x, F i (u x) * ψ x ∂μ) l
      (𝓝 (∫ x, f (u x) * ψ x ∂μ)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -M) (b := M)).bddAbove_image hf.norm.continuousOn
  have hunif :=
    tendstoLocallyUniformly_iff_forall_isCompact.mp hconv (Icc (-M) M) isCompact_Icc
  have hbound : ∀ᶠ i in l, ∀ r ∈ Icc (-M) M, ‖F i r‖ ≤ C + 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif 1 zero_lt_one] with i hi r hr
    calc
      ‖F i r‖ ≤ ‖f r‖ + ‖f r - F i r‖ := norm_le_norm_add_norm_sub _ _
      _ ≤ C + 1 := add_le_add (hC (mem_image_of_mem _ hr))
        (by simpa only [dist_eq_norm] using (hi r hr).le)
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ (C + 1) * ‖ψ x‖)
  · exact Eventually.of_forall fun i ↦
      ((hF i).comp_aestronglyMeasurable hu).mul hψ.aestronglyMeasurable
  · filter_upwards [hbound] with i hi
    filter_upwards [hM] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hi _ (abs_le.mp hx)) (norm_nonneg _)
  · exact hψ.norm.const_mul _
  · exact Eventually.of_forall fun x ↦
      (hconv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (u x))).mul_const (ψ x)

end MeasureTheory
