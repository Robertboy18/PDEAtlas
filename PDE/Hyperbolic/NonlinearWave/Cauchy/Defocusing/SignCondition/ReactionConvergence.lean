/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.Potential

/-!
# Convergence of arbitrary-growth sign-preserving reactions

A common integral bound on the product u f(u) gives uniform integrability of the reaction on a
finite measure space, provided the reactions are uniformly bounded on bounded amplitude intervals.
Pointwise domination by a continuous original reaction supplies that bound. Expanding amplitude
agreement then identifies the limit, and Mathlib's Vitali theorem gives convergence in L¹. These are
steps 4 and 5 of the proof of Theorem 1 of Evans, §12.3.1; for the convergence (9) we use the Vitali
theorem in place of Evans's argument with Egorov's theorem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.1, steps 4-5 of the proof of Theorem 1, equation (9).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- Product control and continuous pointwise domination give uniform integrability
of reactions on finite measure spaces. The product norm allows this analytic
lemma to be used independently of the sign condition yielding its bound. -/
theorem uniformIntegrable_reaction_of_product_bound {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℝ → ℝ} {g : ι → ℝ → ℝ} {u : ι → α → ℝ}
    (hf : Continuous f) (hg : ∀ i, Continuous (g i)) (hdom : ∀ i z, |g i z| ≤ |f z|)
    (hu : ∀ i, AEStronglyMeasurable (u i) μ) {M : NNReal}
    (hprod : ∀ i, (∫⁻ x, ‖u i x * g i (u i x)‖ₑ ∂μ) ≤ M) :
    UniformIntegrable (fun i x ↦ g i (u i x)) 1 μ := by
  have hmeas (i : ι) : AEStronglyMeasurable (fun x ↦ g i (u i x)) μ :=
    (hg i).comp_aestronglyMeasurable (hu i)
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top hmeas fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := (M : ENNReal)) ENNReal.coe_ne_top hε.ne'
  have hδR : 0 < (δ : ℝ) := hδ
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ) (δ : ℝ)⁻¹).exists_bound_of_continuousOn
    hf.continuousOn
  let C : NNReal := ⟨max B 0 + 1, by positivity⟩
  refine ⟨C, fun i ↦ ?_⟩
  have htail : AEStronglyMeasurable ({x | C ≤ ‖g i (u i x)‖₊}.indicator (fun x ↦ g i (u i x))) μ :=
    (hmeas i).indicator₀ (nullMeasurableSet_le aemeasurable_const (hmeas i).nnnorm.aemeasurable)
  rw [eLpNorm_one_eq_lintegral_enorm htail]
  have hpoint (x : α) : ‖{x | C ≤ ‖g i (u i x)‖₊}.indicator (fun x ↦ g i (u i x)) x‖ ≤
        (δ : ℝ) * ‖u i x * g i (u i x)‖ := by
    by_cases hx : C ≤ ‖g i (u i x)‖₊
    · rw [indicator_of_mem (show x ∈ {x | C ≤ ‖g i (u i x)‖₊} from hx)]
      have hout : (δ : ℝ)⁻¹ < ‖u i x‖ := by
        by_contra! hb
        have hfB := hB (u i x) (by simpa only [mem_closedBall_zero_iff] using hb)
        have hgB : ‖g i (u i x)‖ ≤ B := (hdom i (u i x)).trans hfB
        have hxR : max B 0 + 1 ≤ ‖g i (u i x)‖ := hx
        linarith [le_max_left B 0]
      have hlarge : 1 ≤ (δ : ℝ) * ‖u i x‖ := by
        have h := mul_le_mul_of_nonneg_left hout.le hδR.le
        rwa [mul_inv_cancel₀ hδR.ne'] at h
      calc
        ‖g i (u i x)‖ = 1 * ‖g i (u i x)‖ := (one_mul _).symm
        _ ≤ ((δ : ℝ) * ‖u i x‖) * ‖g i (u i x)‖ := mul_le_mul_of_nonneg_right hlarge (norm_nonneg _)
        _ = (δ : ℝ) * ‖u i x * g i (u i x)‖ := by rw [norm_mul, mul_assoc]
    · rw [indicator_of_notMem (show x ∉ {x | C ≤ ‖g i (u i x)‖₊} from hx), norm_zero]
      positivity
  have hpointE (x : α) : ‖{x | C ≤ ‖g i (u i x)‖₊}.indicator (fun x ↦ g i (u i x)) x‖ₑ ≤
        (δ : ENNReal) * ‖u i x * g i (u i x)‖ₑ := by
    simpa only [ENNReal.ofReal_mul hδR.le, ENNReal.ofReal_coe_nnreal,
      ofReal_norm] using ENNReal.ofReal_le_ofReal (hpoint x)
  calc
    _ ≤ ∫⁻ x, (δ : ENNReal) * ‖u i x * g i (u i x)‖ₑ ∂μ := lintegral_mono hpointE
    _ = (δ : ENNReal) * ∫⁻ x, ‖u i x * g i (u i x)‖ₑ ∂μ :=
      lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ (δ : ENNReal) * M := mul_le_mul' le_rfl (hprod i)
    _ ≤ ε := hδε.le

/-- Expanding amplitude agreement identifies the reaction along any convergent
scalar net, including subsequences selected by compactness. -/
theorem tendsto_reaction_of_expanding_agreement {ι : Type*} {l : Filter ι} {f : ℝ → ℝ}
    {g : ι → ℝ → ℝ} {r v : ι → ℝ} {z : ℝ} (hf : Continuous f)
    (hagree : ∀ i, EqOn (g i) f (Metric.closedBall 0 (r i))) (hr : Tendsto r l atTop)
    (hv : Tendsto v l (𝓝 z)) :
    Tendsto (fun i ↦ g i (v i)) l (𝓝 (f z)) := by
  have hsmall : ∀ᶠ i in l, ‖v i‖ < ‖z‖ + 1 := hv.norm.eventually (gt_mem_nhds (lt_add_one ‖z‖))
  have hlarge : ∀ᶠ i in l, ‖z‖ + 1 ≤ r i := hr.eventually (eventually_ge_atTop _)
  apply ((hf.tendsto z).comp hv).congr'
  filter_upwards [hsmall, hlarge] with i hi hri
  exact (hagree i (by simpa only [mem_closedBall_zero_iff] using hi.le.trans hri)).symm

/-- The limiting reaction is integrable and the approximate reactions converge in
L¹. The only nonlinear bound assumed is the uniform product estimate. -/
theorem integrable_reaction_and_tendsto_L1 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} {u : ℕ → α → ℝ} {v : α → ℝ} {r : ℕ → ℝ}
    (hf : Continuous f) (hg : ∀ i, Continuous (g i)) (hdom : ∀ i z, |g i z| ≤ |f z|)
    (hu : ∀ i, AEStronglyMeasurable (u i) μ) {M : NNReal}
    (hprod : ∀ i, (∫⁻ x, ‖u i x * g i (u i x)‖ₑ ∂μ) ≤ M)
    (hagree : ∀ i, EqOn (g i) f (Metric.closedBall 0 (r i))) (hr : Tendsto r atTop atTop)
    (hv : ∀ᵐ x ∂μ, Tendsto (fun i ↦ u i x) atTop (𝓝 (v x))) :
    Integrable (fun x ↦ f (v x)) μ ∧
      Tendsto (fun i ↦ eLpNorm (fun x ↦ g i (u i x) - f (v x)) 1 μ) atTop (𝓝 0) := by
  have hui := uniformIntegrable_reaction_of_product_bound hf hg hdom hu hprod
  have ht : ∀ᵐ x ∂μ, Tendsto (fun i ↦ g i (u i x)) atTop (𝓝 (f (v x))) := by
    filter_upwards [hv] with x hx using tendsto_reaction_of_expanding_agreement hf hagree hr hx
  exact ⟨hui.integrable_of_ae_tendsto ht, tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
      (fun i ↦ (hg i).comp_aestronglyMeasurable (hu i)) (hui.memLp_of_ae_tendsto ht) hui.1 ht⟩

/-- Local convergence in measure suffices for the nonlinear limit. Uniform product
control derives integrability of the limit and upgrades the whole sequence to L¹,
without choosing a common pointwise representative on all finite cylinders. -/
theorem integrable_reaction_and_tendsto_L1_of_tendstoInMeasure {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} {u : ℕ → α → ℝ} {v : α → ℝ}
    {r : ℕ → ℝ} (hf : Continuous f) (hg : ∀ i, Continuous (g i)) (hdom : ∀ i z, |g i z| ≤ |f z|)
    (hu : ∀ i, AEStronglyMeasurable (u i) μ) {M : NNReal}
    (hprod : ∀ i, (∫⁻ x, ‖u i x * g i (u i x)‖ₑ ∂μ) ≤ M)
    (hagree : ∀ i, EqOn (g i) f (Metric.closedBall 0 (r i))) (hr : Tendsto r atTop atTop)
    (hv : TendstoInMeasure μ u atTop v) :
    Integrable (fun x ↦ f (v x)) μ ∧
      Tendsto (fun i ↦ eLpNorm (fun x ↦ g i (u i x) - f (v x)) 1 μ) atTop (𝓝 0) := by
  have hmeas (i : ℕ) : AEStronglyMeasurable (fun x ↦ g i (u i x)) μ :=
    (hg i).comp_aestronglyMeasurable (hu i)
  have ht : TendstoInMeasure μ (fun i x ↦ g i (u i x)) atTop (fun x ↦ f (v x)) := by
    refine (exists_seq_tendstoInMeasure_atTop_iff hmeas).mpr fun ns hns ↦ ?_
    obtain ⟨ms, hms, hae⟩ := (hv.comp hns.tendsto_atTop).exists_seq_tendsto_ae
    refine ⟨ms, hms, ?_⟩
    filter_upwards [hae] with x hx
    exact tendsto_reaction_of_expanding_agreement hf (fun i ↦ hagree (ns (ms i)))
      (hr.comp (hns.comp hms).tendsto_atTop) hx
  have hui := uniformIntegrable_reaction_of_product_bound hf hg hdom hu hprod
  exact ⟨hui.integrable_of_tendstoInMeasure ht,
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hmeas
      (hui.memLp_of_tendstoInMeasure ht) hui.1 ht⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
