/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.Tactic.Positivity.Finset

/-!
# Transferring compactness between finite Lebesgue exponents

A uniform bound at a higher exponent gives uniform integrability at every
strictly smaller finite exponent. On a finite measure space, an inclusion
compact at one exponent and bounded at a higher exponent is compact at every
finite intermediate target. The three maps represent the same functions almost
everywhere. This is the step from one exponent to all subcritical exponents in the
Rellich–Kondrachov theorem.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

/-- A uniformly `Lʳ`-bounded family is uniformly integrable in `Lᑫ` for
`1 ≤ q < r < ∞`, on an arbitrary measure space. -/
theorem unifIntegrable_of_eLpNorm_bound
    {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {q r : ℝ≥0} {f : ι → α → E}
    (hq_one : 1 ≤ q) (hqr : q < r)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (C : ℝ≥0)
    (hC : ∀ i, eLpNorm (f i) (r : ℝ≥0∞) μ ≤ C) :
    UnifIntegrable f (q : ℝ≥0∞) μ := by
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast (zero_lt_one.trans_le hq_one)
  let gap : ℝ := 1 / (q : ℝ) - 1 / (r : ℝ)
  have hgap : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hqpos (by exact_mod_cast hqr))
  have htend : Tendsto (fun d : ℝ≥0∞ ↦ (C : ℝ≥0∞) * d ^ gap) (𝓝 0) (𝓝 0) :=
    ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top hgap
  apply unifIntegrable_iff.2
  intro ε hε
  obtain ⟨δ, hδ, hdest⟩ := ENNReal.nhds_zero_basis_Iic.eventually_iff.1
    (htend.eventually (gt_mem_nhds hε))
  refine ⟨δ, hδ, fun i s hμs ↦ ?_⟩
  have hmeas : AEStronglyMeasurable (f i) (μ.restrict s) :=
    (hf i).mono_measure Measure.restrict_le_self
  have hqrE : (q : ℝ≥0∞) ≤ (r : ℝ≥0∞) := by exact_mod_cast hqr.le
  calc
    eLpNorm (f i) (q : ℝ≥0∞) (μ.restrict s)
        ≤ eLpNorm (f i) (r : ℝ≥0∞) (μ.restrict s) *
          (μ.restrict s) univ ^ (1 / (q : ℝ≥0∞).toReal - 1 / (r : ℝ≥0∞).toReal) :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqrE hmeas
    _ ≤ (C : ℝ≥0∞) * (μ s) ^ gap := by
      simp only [Measure.restrict_apply_univ, ENNReal.coe_toReal, gap]
      gcongr
      exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC i)
    _ ≤ (C : ℝ≥0∞) * δ ^ gap := by gcongr
    _ ≤ ε := (hdest (Set.mem_Iic.mpr le_rfl)).le

end MeasureTheory

/-- Compactness into one `Lp` space and boundedness into a higher exponent
give compactness at a strictly smaller finite target exponent. All three maps
represent the same functions; the source is any real normed space. -/
theorem IsCompactOperator.into_Lp_of_higher_exponent
    {α X E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [IsFiniteMeasure μ]
    {s : ℝ≥0∞} {q r : ℝ≥0}
    [Fact (1 ≤ s)] [Fact (1 ≤ (q : ℝ≥0∞))] [Fact (1 ≤ (r : ℝ≥0∞))]
    {Js : X →L[ℝ] Lp E s μ} (hbase : IsCompactOperator Js)
    (Jq : X →L[ℝ] Lp E (q : ℝ≥0∞) μ)
    (Jr : X →L[ℝ] Lp E (r : ℝ≥0∞) μ)
    (hqr : q < r)
    (hsq : ∀ u, (Js u : α → E) =ᵐ[μ] (Jq u : α → E))
    (hrq : ∀ u, (Jr u : α → E) =ᵐ[μ] (Jq u : α → E)) :
    IsCompactOperator Jq := by
  have hq_one : 1 ≤ q := by exact_mod_cast (Fact.out : 1 ≤ (q : ℝ≥0∞))
  have hbound {t : ℝ≥0∞} [Fact (1 ≤ t)] (J : X →L[ℝ] Lp E t μ)
      (u : X) (hu : ‖u‖ ≤ 1) : eLpNorm (J u : α → E) t μ ≤ ‖J‖₊ := by
    rw [← Lp.enorm_def]
    exact_mod_cast (J.le_opNorm u).trans
      ((mul_le_mul_of_nonneg_left hu J.opNorm_nonneg).trans_eq (mul_one _))
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (Jq : X →ₗ[ℝ] Lp E (q : ℝ≥0∞) μ) zero_lt_one).2
  rw [isCompact_iff_isSeqCompact]
  intro x hx
  have hεpos (m : ℕ) : 0 < (1 / ((m : ℝ) + 1)) := by positivity
  choose y hy hxy using fun m ↦
    Metric.mem_closure_iff.1 (hx m) (1 / ((m : ℝ) + 1)) (hεpos m)
  choose U hU hyU using fun m ↦ hy m
  have hUnorm (m : ℕ) : ‖U m‖ ≤ 1 := mem_closedBall_zero_iff.mp (hU m)
  have hyU' (m : ℕ) : Jq (U m) = y m := hyU m
  obtain ⟨K, hKcompact, hKsub⟩ := hbase.image_closedBall_subset_compact 1
  obtain ⟨vs, _, φ, hφ, hsTend⟩ :=
    hKcompact.tendsto_subseq (fun m ↦ hKsub ⟨U m, hU m, rfl⟩)
  let fseq : ℕ → α → E := fun m ↦ Jq (U (φ m))
  have hsMeasure : TendstoInMeasure μ fseq atTop (vs : α → E) :=
    (tendstoInMeasure_of_tendsto_Lp hsTend).congr
      (fun m ↦ hsq (U (φ m))) EventuallyEq.rfl
  have hmeas (m : ℕ) : AEStronglyMeasurable (fseq m) μ :=
    Lp.aestronglyMeasurable _
  have hrBound (m : ℕ) : eLpNorm (fseq m) (r : ℝ≥0∞) μ ≤ ‖Jr‖₊ := by
    rw [← eLpNorm_congr_ae (hrq (U (φ m)))]
    exact hbound Jr _ (hUnorm _)
  have hUI : UnifIntegrable fseq (q : ℝ≥0∞) μ :=
    unifIntegrable_of_eLpNorm_bound hq_one hqr hmeas ‖Jr‖₊ hrBound
  have hUniform : UniformIntegrable fseq (q : ℝ≥0∞) μ :=
    ⟨hUI, ⟨‖Jq‖₊, fun m ↦ hbound Jq _ (hUnorm _)⟩⟩
  have hvsMemQ : MemLp (vs : α → E) (q : ℝ≥0∞) μ :=
    hUniform.memLp_of_tendstoInMeasure hsMeasure
  have hTight : UnifTight fseq (q : ℝ≥0∞) μ := by
    intro ε _
    exact ⟨univ, measure_ne_top _ _, fun _ ↦ by simp⟩
  have hVitali : Tendsto
      (fun m ↦ eLpNorm (fseq m - (vs : α → E)) (q : ℝ≥0∞) μ) atTop (𝓝 0) :=
    tendsto_Lp_of_tendstoInMeasure (Fact.out : 1 ≤ (q : ℝ≥0∞)) (by simp)
      hmeas hvsMemQ hUI hTight hsMeasure
  let vq : Lp E (q : ℝ≥0∞) μ := hvsMemQ.toLp (vs : α → E)
  have hqTend : Tendsto (fun m ↦ Jq (U (φ m))) atTop (𝓝 vq) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ hvsMemQ).2 hVitali
  have hvqClosure : vq ∈ closure (Jq '' Metric.closedBall (0 : X) 1) := by
    apply isClosed_closure.mem_of_tendsto hqTend
    exact Eventually.of_forall fun m ↦ subset_closure ⟨U (φ m), hU (φ m), rfl⟩
  have happrox : Tendsto (fun m ↦ dist (x (φ m)) (Jq (U (φ m)))) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun m ↦ 1 / (((φ m : ℕ) : ℝ) + 1))
    · exact fun _ ↦ dist_nonneg
    · intro m
      rw [hyU' (φ m)]
      exact (hxy (φ m)).le
    · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hxTend : Tendsto (x ∘ φ) atTop (𝓝 vq) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero
    · exact fun _ ↦ dist_nonneg
    · exact fun m ↦ dist_triangle _ (Jq (U (φ m))) _
    · simpa [Function.comp_apply] using
        happrox.add (tendsto_iff_dist_tendsto_zero.1 hqTend)
  exact ⟨vq, hvqClosure, φ, hφ, hxTend⟩
