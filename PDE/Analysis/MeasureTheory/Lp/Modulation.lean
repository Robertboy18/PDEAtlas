/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import PDE.Analysis.MeasureTheory.DominatedLp

/-!
# Scalar modulation and L2 rotation columns

A bounded continuous scalar function of a measurable frequency acts as a
contraction on Lp. At finite exponents this action is strongly continuous in
the modulation parameter. The column (-sin, cos) gives an exact L2 isometry
into the Hilbert direct sum, jointly continuous in the parameter and input.

These operators use Mathlib's Holder multiplication map on Lp classes. Their
representative lemmas state the pointwise formulas almost everywhere.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory.Lp

section Modulation

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A bounded scalar modulation defines an actual continuous multiplier on Lp. -/
noncomputable def modulationCLM {m : ℝ → ℝ} (hm : Continuous m)
    (hb : ∀ r, |m r| ≤ 1) {ω : α → ℝ} (hω : Measurable ω) (t : ℝ) :
    Lp E p μ →L[ℝ] Lp E p μ :=
  (ContinuousLinearMap.lsmul ℝ ℝ).holderL μ ∞ p p
    ((memLp_top_of_bound (hm.measurable.comp (hω.mul_const t)).aestronglyMeasurable 1
      (.of_forall fun x ↦ hb (ω x * t))).toLp (fun x ↦ m (ω x * t)))

/-- The multiplier is represented by the pointwise modulation almost everywhere. -/
theorem modulationCLM_coeFn {m : ℝ → ℝ} (hm : Continuous m)
    (hb : ∀ r, |m r| ≤ 1) {ω : α → ℝ} (hω : Measurable ω) (t : ℝ) (u : Lp E p μ) :
    modulationCLM hm hb hω t u =ᵐ[μ] fun x ↦ m (ω x * t) • u x := by
  unfold modulationCLM
  rw [ContinuousLinearMap.holderL_apply_apply]
  apply (ContinuousLinearMap.coeFn_holder _ _ u).trans
  filter_upwards [(memLp_top_of_bound (hm.measurable.comp (hω.mul_const t)).aestronglyMeasurable 1
      (.of_forall fun x ↦ hb (ω x * t))).coeFn_toLp] with x ha
  simpa only [ContinuousLinearMap.lsmul_apply, Function.comp_def] using
    congrArg (fun r : ℝ ↦ r • u x) ha

/-- Unit bounded modulation is a contraction. -/
theorem norm_modulationCLM_apply_le {m : ℝ → ℝ} (hm : Continuous m)
    (hb : ∀ r, |m r| ≤ 1) {ω : α → ℝ} (hω : Measurable ω) (t : ℝ) (u : Lp E p μ) :
    ‖modulationCLM hm hb hω t u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [modulationCLM_coeFn hm hb hω t u] with x hx
  rw [hx, norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb _)

/-- Bounded continuous modulation is strongly continuous at finite Lp exponents. -/
theorem continuous_modulationCLM_apply (hp : p ≠ ∞) {m : ℝ → ℝ} (hm : Continuous m)
    (hb : ∀ r, |m r| ≤ 1) {ω : α → ℝ} (hω : Measurable ω) (u : Lp E p μ) :
    Continuous (fun t : ℝ ↦ modulationCLM hm hb hω t u) := by
  have hmemb (t : ℝ) : MemLp (fun x ↦ m (ω x * t) • u x) p μ := by
    apply (Lp.memLp u).of_le
      ((hm.measurable.comp (hω.mul_const t)).aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable u))
    exact .of_forall fun x ↦ by
      change ‖m (ω x * t) • u x‖ ≤ ‖u x‖
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hb _)
  have he (t : ℝ) : modulationCLM hm hb hω t u =
      (hmemb t).toLp (fun x ↦ m (ω x * t) • u x) := by
    apply Lp.ext
    exact (modulationCLM_coeFn hm hb hω t u).trans (hmemb t).coeFn_toLp.symm
  simp_rw [he]
  refine continuous_iff_seqContinuous.mpr ?_
  intro v t hv
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n ↦ hmemb (v n)) _ (hmemb t)).mpr
  refine tendsto_Lp_of_tendsto_ae_of_ae_norm_le (Fact.out : 1 ≤ p) hp
    (fun n ↦ (hmemb (v n)).aestronglyMeasurable) (hmemb t) (Lp.memLp u)
    (fun n ↦ .of_forall fun x ↦ ?_) (.of_forall fun x ↦ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb _)
  · exact ((hm.continuousAt.tendsto.comp (tendsto_const_nhds.mul hv)).smul
      tendsto_const_nhds)

end Modulation

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The column (-sin, cos) of the rotation at an arbitrary measurable frequency. -/
noncomputable def rotationColumn {ω : α → ℝ} (hω : Measurable ω) (t : ℝ) :
    Lp E 2 μ →L[ℝ] WithLp 2 (Lp E 2 μ × Lp E 2 μ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    ((-modulationCLM Real.continuous_sin Real.abs_sin_le_one hω t).prod
      (modulationCLM Real.continuous_cos Real.abs_cos_le_one hω t))

/-- The first component is multiplication by the negative sine. -/
theorem rotationColumn_fst_ae {ω : α → ℝ} (hω : Measurable ω) (t : ℝ) (u : Lp E 2 μ) :
    (rotationColumn hω t u).fst =ᵐ[μ] fun x ↦ -Real.sin (ω x * t) • u x := by
  change (-modulationCLM Real.continuous_sin Real.abs_sin_le_one hω t u : Lp E 2 μ) =ᵐ[μ] _
  filter_upwards [Lp.coeFn_neg (modulationCLM Real.continuous_sin
    Real.abs_sin_le_one hω t u),
    modulationCLM_coeFn Real.continuous_sin Real.abs_sin_le_one hω t u] with x hn hs
  simp only [hn, Pi.neg_apply, hs, neg_smul]

/-- The cosine component of the rotation column. -/
theorem rotationColumn_snd_ae {ω : α → ℝ} (hω : Measurable ω) (t : ℝ) (u : Lp E 2 μ) :
    (rotationColumn hω t u).snd =ᵐ[μ] fun x ↦ Real.cos (ω x * t) • u x :=
  modulationCLM_coeFn Real.continuous_cos Real.abs_cos_le_one hω t u

/-- The rotation column preserves the L2 energy exactly. -/
theorem norm_rotationColumn {ω : α → ℝ} (hω : Measurable ω) (t : ℝ) (u : Lp E 2 μ) :
    ‖rotationColumn hω t u‖ = ‖u‖ := by
  have hsq (v : Lp E 2 μ) : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  have hi (v : Lp E 2 μ) : Integrable (fun x ↦ ‖v x‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) v v
  have he : ‖rotationColumn hω t u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, hsq, hsq, hsq, ← integral_add (hi _) (hi _)]
    apply integral_congr_ae
    filter_upwards [rotationColumn_fst_ae hω t u, rotationColumn_snd_ae hω t u] with x hs hc
    rw [hs, hc, norm_smul, norm_smul, _root_.norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, sq_abs, sq_abs, ← add_mul, Real.sin_sq_add_cos_sq, one_mul]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

/-- The rotation column is strongly continuous in its time parameter. -/
theorem continuous_rotationColumn_apply {ω : α → ℝ} (hω : Measurable ω) (u : Lp E 2 μ) :
    Continuous (fun t : ℝ ↦ rotationColumn hω t u) := by
  exact (WithLp.prod_continuous_toLp 2 _ _).comp
    (((continuous_modulationCLM_apply (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      Real.continuous_sin Real.abs_sin_le_one hω u).neg).prodMk
      (continuous_modulationCLM_apply (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        Real.continuous_cos Real.abs_cos_le_one hω u))

/-- The rotation column acts jointly continuously in time and its L2 input. -/
theorem continuous_rotationColumn {ω : α → ℝ} (hω : Measurable ω) :
    Continuous (fun z : ℝ × Lp E 2 μ ↦ rotationColumn hω z.1 z.2) := by
  refine continuous_prod_of_continuous_lipschitzWith' _ 1 ?_
    (continuous_rotationColumn_apply hω)
  intro t
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simpa only [_root_.dist_eq_norm, NNReal.coe_one, one_mul, ← map_sub,
    norm_rotationColumn] using (le_refl ‖u - v‖)

end MeasureTheory.Lp
