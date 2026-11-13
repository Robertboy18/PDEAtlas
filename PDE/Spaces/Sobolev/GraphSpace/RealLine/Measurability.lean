/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.BochnerIntegral
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.SecondOrder.Convergence

/-!
# Measurability of real-line Sobolev families

Jointly measurable spatial representatives determine strongly measurable H²
graphs. Distances in L² are measurable spatial integrals; injectivity of the
Sobolev base coordinate then supplies graph measurability. In particular, this
argument does not require continuity of the family in its graph norm.
Bounded measurable H¹ families also have integrable representatives along
continuous paths on finite time intervals.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace unitInterval
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

private theorem stronglyMeasurable_of_measurable_dist
    {T E : Type*} [MeasurableSpace T] [MetricSpace E] [SeparableSpace E] [Nonempty E]
    {f : T → E} (hdist : ∀ e, Measurable (fun t ↦ dist (f t) e)) :
    StronglyMeasurable f := by
  have hcube : StronglyMeasurable
      (fun t n ↦ Metric.PiNatEmbed.distDenseSeq E n (f t)) := by
    apply Measurable.stronglyMeasurable
    apply Measurable.of_eval
    intro n
    exact continuous_projIcc.measurable.comp (hdist (denseSeq E n))
  have hembed := (Metric.PiNatEmbed.isUniformEmbedding_embed
    (Metric.PiNatEmbed.injective_distDenseSeq (X := E))).isEmbedding
  have hlift : StronglyMeasurable
      (fun t ↦ Metric.PiNatEmbed.toPiNat (f t) :
        T → Metric.PiNatEmbed E (fun _ : ℕ ↦ I) (Metric.PiNatEmbed.distDenseSeq E)) :=
    (Embedding.comp_stronglyMeasurable_iff hembed).mp hcube
  exact Metric.PiNatEmbed.continuous_distDenseSeq_inv.comp_stronglyMeasurable hlift

/-- A jointly measurable representative of each Sobolev base row gives strong
measurability of the whole graph, without continuity of its higher rows. -/
theorem stronglyMeasurable_hk_of_joint_representative
    {T : Type*} [MeasurableSpace T] {k : ℕ} (W : T → W^{k,2}(ℝ^1))
    {v : T → ℝ → ℝ} (hv : StronglyMeasurable (Function.uncurry v))
    (hrep : ∀ t, (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM (W t)) : ℝ → ℝ)
      =ᵐ[volume] v t) :
    StronglyMeasurable W := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℝ 2 (volume : Measure ℝ)) :=
    Lp.SecondCountableTopology
  let U : T → Lp ℝ 2 (volume : Measure ℝ) :=
    fun t ↦ oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM (W t))
  have hU : StronglyMeasurable U := by
    apply stronglyMeasurable_of_measurable_dist
    intro q
    have hq : StronglyMeasurable (fun z : T × ℝ ↦ q z.2) :=
      (Lp.stronglyMeasurable q).comp_measurable measurable_snd
    have hdist : Measurable (fun t ↦ √(∫ x, ‖v t x - q x‖ ^ 2)) :=
      ((hv.sub hq).norm.pow 2).integral_prod_right'.measurable.sqrt
    have heq (t : T) : dist (U t) q ^ 2 = ∫ x, ‖v t x - q x‖ ^ 2 := by
      rw [dist_eq_norm, Lp.norm_sq_eq_integral_norm_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (U t) q, hrep t] with x hx hr
      simp only [hx, Pi.sub_apply, U, hr]
    simpa only [← heq, Real.sqrt_sq dist_nonneg] using hdist
  apply stronglyMeasurable_of_wkpBaseCoordinateCLM isOpen_univ W
  simpa only [U, oneDimensionalPullbackL2_pushforward] using
    oneDimensionalPullbackL2.continuous.comp_stronglyMeasurable hU

/-- The H² specialization used for the derivative evolution. -/
theorem stronglyMeasurable_h2_of_joint_representative
    {T : Type*} [MeasurableSpace T] (W : T → W^{2,2}(ℝ^1))
    {v : T → ℝ → ℝ} (hv : StronglyMeasurable (Function.uncurry v))
    (hrep : ∀ t, (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM (W t)) : ℝ → ℝ)
      =ᵐ[volume] v t) :
    StronglyMeasurable W :=
  stronglyMeasurable_hk_of_joint_representative W hv hrep

/-- A measurable H¹ graph has a jointly measurable canonical representative.
Evaluation is continuous in the graph at each fixed point, and spatial
continuity supplies the other variable. -/
theorem stronglyMeasurable_realLineRepresentative
    {T : Type*} [MeasurableSpace T] {W : T → W^{1,2}(ℝ^1)}
    (hW : StronglyMeasurable W) :
    StronglyMeasurable (fun z : T × ℝ ↦ realLineRepresentative (W z.1) z.2) := by
  let : MeasurableSpace (W^{1,2}(ℝ^1)) := borel _
  have : BorelSpace (W^{1,2}(ℝ^1)) := ⟨rfl⟩
  have hev : Measurable
      (fun z : ℝ × W^{1,2}(ℝ^1) ↦ realLineRepresentative z.2 z.1) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun U ↦ continuous_realLineRepresentative U)
      (fun x ↦ (lipschitzWith_realLineRepresentative_eval x).continuous.measurable)
  exact (hev.comp (measurable_snd.prodMk (hW.measurable.comp measurable_fst))).stronglyMeasurable

/-- Composition by a jointly measurable family of spatial maps preserves
time measurability whenever its H² graph is known to exist. The graph action
itself need not be measurable in operator norm. -/
theorem stronglyMeasurable_h2_pullback
    {T : Type*} [MeasurableSpace T] {e : T → ℝ → ℝ}
    (he : Measurable (Function.uncurry e))
    (P : T → W^{2,2}(ℝ^1) →L[ℝ] W^{2,2}(ℝ^1))
    (hP : ∀ t W, realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (P t W)) =
      fun x ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W) (e t x))
    {W : T → W^{2,2}(ℝ^1)} (hW : StronglyMeasurable W) :
    StronglyMeasurable (fun t ↦ P t (W t)) := by
  apply stronglyMeasurable_h2_of_joint_representative (fun t ↦ P t (W t))
    (v := fun t x ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W t)) (e t x))
    ((stronglyMeasurable_realLineRepresentative
      ((lowerOrderCLM (by decide : 1 ≤ 2)).continuous.comp_stronglyMeasurable hW)).comp_measurable
        (measurable_fst.prodMk he))
  intro t
  exact (realLineRepresentative_lowerOrder_ae (P t (W t))).trans
    (Filter.EventuallyEq.of_eq (hP t (W t)))

/-- A bounded strongly measurable H¹ family has integrable continuous
representatives along a continuous path on a finite time slab. -/
theorem intervalIntegrable_h1_along_flow
    {T : ℝ} {hT : 0 ≤ T} {X : ℝ → ℝ → ℝ}
    (hX : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ X p.1 p.2))
    {S : Icc (0 : ℝ) T → W^{1,2}(ℝ^1)} (hSm : StronglyMeasurable S)
    {C : ℝ} (hSnorm : ∀ t, ‖S t‖ ≤ C) (a : ℝ) (t : Icc (0 : ℝ) T) :
    IntervalIntegrable (fun s ↦ realLineRepresentative (S (projIcc 0 T hT s))
      (X a s)) volume 0 t := by
  have hpath : Measurable (fun t : Icc (0 : ℝ) T ↦ (t, X a t)) :=
    measurable_id.prodMk (hX.comp (continuous_const.prodMk continuous_id)).measurable
  let F (t : Icc (0 : ℝ) T) := realLineRepresentative (S t) (X a t)
  have hraw := (stronglyMeasurable_realLineRepresentative hSm).comp_measurable hpath
  have hFm : StronglyMeasurable F := by
    simpa only [Function.comp_def, F] using hraw
  have hFnorm (s : Icc (0 : ℝ) T) : ‖F s‖ ≤ 2 * C :=
    (norm_realLineRepresentative_le (S s) (X a s)).trans
      (mul_le_mul_of_nonneg_left (hSnorm s) (by norm_num))
  have hi : IntegrableOn (fun s ↦ F (projIcc 0 T hT s)) (Icc (0 : ℝ) T) volume := by
    apply (integrableOn_const (C := 2 * C)
      (hs := measure_Icc_lt_top.ne)).mono'
      ((hFm.comp_measurable continuous_projIcc.measurable).aestronglyMeasurable.restrict)
    exact Filter.Eventually.of_forall (fun s ↦ hFnorm _)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le t.property.1).mpr
  apply (hi.mono_set (Icc_subset_Icc_right t.property.2)).congr_fun
  · intro s hs
    have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans t.property.2⟩
    simp only [F, projIcc_of_mem hT hsI]
  · exact measurableSet_Icc

end SobolevSpace.GraphSpace
