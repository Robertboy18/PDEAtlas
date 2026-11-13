/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.VectorValued.Estimate
import PDE.Spaces.Sobolev.Approximation.VectorValued.Mollification.Graph

/-!
# Banach-valued Morrey representatives

Mollification converges in the Sobolev graph norm at every finite exponent. The
Morrey estimate makes its continuous representatives uniformly Cauchy. Completeness
of the codomain gives a bounded continuous limit, and an almost-everywhere convergent
subsequence of the base `Lp` coordinates identifies that limit with the original class.
The pointwise estimates then give the sharp exponent `1 - n/p`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev Topology BoundedContinuousFunction

namespace SobolevSpace.VectorValued

open Approximation GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem dist_representatives_le (hp : (n : ℝ≥0∞) < p)
    (U V : W^{1,p}(ℝ^n; F)) (f g : ℝ^n →ᵇ F)
    (hf : (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[volume] f)
    (hg : (V.val (baseIndex n 1) : ℝ^n → F) =ᵐ[volume] g) :
    dist f g ≤ morreyConstant n p hp * dist U V := by
  rw [dist_eq_norm, dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (morreyConstant_nonneg hp) (norm_nonneg _))).2
  have hsub : ((U - V).val (baseIndex n 1) : ℝ^n → F) =ᵐ[volume]
      fun x ↦ f x - g x := by
    have h := Lp.coeFn_sub (U.val (baseIndex n 1)) (V.val (baseIndex n 1))
    simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ] at h
    filter_upwards [h, hf, hg] with x hx hfx hgx
    exact hx.trans (congrArg₂ (· - ·) hfx hgx)
  exact norm_apply_le_morreyConstant hp (U - V) (f.continuous.sub g.continuous) hsub

/-- Every whole-space Banach-valued Sobolev class with finite `p > n` has a bounded
continuous representative. Dimension zero and `p = 1` in that dimension are included. -/
theorem exists_boundedContinuous_representative (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞)
    (U : W^{1,p}(ℝ^n; F)) :
    ∃ f : ℝ^n →ᵇ F, (f : ℝ^n → F) =ᵐ[volume] (U.val (baseIndex n 1) : ℝ^n → F) := by
  let ε (m : ℕ) : ℝ := 1 / (m + 1)
  have hε (m : ℕ) : 0 < ε m := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let V (m : ℕ) := mollify (standardMollifier n) (hε m) hfinite U
  have hV : Tendsto V atTop (𝓝 U) :=
    mollify_tendsto (standardMollifier n) hfinite U ε hε hε0
  choose f hf hbase using fun m ↦
    mollify_has_smooth_representative (standardMollifier n) (hε m) hfinite U
  let g (m : ℕ) : ℝ^n →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup
    (f m) (hf m).continuous (morreyConstant n p hp * ‖V m‖)
    (norm_apply_le_morreyConstant hp (V m) (hf m).continuous (hbase m))
  have hdist (m j : ℕ) : dist (g m) (g j) ≤ morreyConstant n p hp * dist (V m) (V j) :=
    dist_representatives_le hp (V m) (V j) (g m) (g j) (hbase m) (hbase j)
  have hcauchy : CauchySeq g := by
    obtain ⟨b, _, hb, hb0⟩ := cauchySeq_iff_le_tendsto_0.mp hV.cauchySeq
    refine cauchySeq_of_le_tendsto_0 (fun j ↦ morreyConstant n p hp * b j) ?_ ?_
    · intro m j N hm hj
      exact (hdist m j).trans
        (mul_le_mul_of_nonneg_left (hb m j N hm hj) (morreyConstant_nonneg hp))
    · simpa using tendsto_const_nhds.mul hb0
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hLp := ((coordinateCLM (baseIndex n 1)).continuous.tendsto U).comp hV
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hLp).exists_seq_tendsto_ae
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ] at hae
  have hall : ∀ᵐ x ∂volume, ∀ m, (V m).val (baseIndex n 1) x = g m x :=
    ae_all_iff.mpr hbase
  refine ⟨v, ?_⟩
  filter_upwards [hae, hall] with x hx hxg
  have hpoint : Tendsto (fun m ↦ g m x) atTop (𝓝 (v x)) :=
    ((BoundedContinuousFunction.evalCLM ℝ x).continuous.tendsto v).comp hv
  have hsub : Tendsto (fun j ↦ g (ns j) x) atTop
      (𝓝 (U.val (baseIndex n 1) x)) := by
    apply hx.congr'
    filter_upwards with j
    exact hxg (ns j)
  exact tendsto_nhds_unique (hpoint.comp hns.tendsto_atTop) hsub

/-- The unique continuous Morrey representative, obtained as a uniform limit of
Banach-valued mollifications. -/
def morreyRepresentative (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞)
    (U : W^{1,p}(ℝ^n; F)) : ℝ^n →ᵇ F :=
  (exists_boundedContinuous_representative hp hfinite U).choose

/-- The Morrey representative is a representative of the base `Lp` coordinate. -/
theorem morreyRepresentative_ae (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞)
    (U : W^{1,p}(ℝ^n; F)) :
    (morreyRepresentative hp hfinite U : ℝ^n → F) =ᵐ[volume]
      (U.val (baseIndex n 1) : ℝ^n → F) :=
  (exists_boundedContinuous_representative hp hfinite U).choose_spec

/-- The sup norm of the Morrey representative is controlled by the graph norm. -/
theorem norm_morreyRepresentative_le (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞)
    (U : W^{1,p}(ℝ^n; F)) :
    ‖morreyRepresentative hp hfinite U‖ ≤ morreyConstant n p hp * ‖U‖ := by
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (morreyConstant_nonneg hp) (norm_nonneg U))).2
  exact norm_apply_le_morreyConstant hp U (morreyRepresentative hp hfinite U).continuous
    (morreyRepresentative_ae hp hfinite U).symm

/-- Hölder continuity of the Banach-valued representative with exponent `1 - n/p`. -/
theorem holderWith_morreyRepresentative (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞)
    (U : W^{1,p}(ℝ^n; F)) :
    HolderWith (morreyConstant n p hp * ‖U‖).toNNReal (morreyExponent n p).toNNReal
      (morreyRepresentative hp hfinite U) := by
  have hgamma : 0 ≤ morreyExponent n p := by
    by_cases hn : 0 < n
    · exact (morreyExponent_pos hn hp).le
    · have : n = 0 := by omega
      simp [this, morreyExponent]
  intro x y
  have h := norm_sub_le_morreyConstant hp U
    (morreyRepresentative hp hfinite U).continuous (morreyRepresentative_ae hp hfinite U).symm x y
  have hC := mul_nonneg (morreyConstant_nonneg hp) (norm_nonneg U)
  rw [edist_dist, edist_dist, Real.coe_toNNReal _ hgamma]
  change ENNReal.ofReal (dist (morreyRepresentative hp hfinite U x)
    (morreyRepresentative hp hfinite U y)) ≤
      ENNReal.ofReal (morreyConstant n p hp * ‖U‖) *
        ENNReal.ofReal (dist x y) ^ morreyExponent n p
  rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg hgamma, ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (by simpa only [dist_eq_norm] using h)

end SobolevSpace.VectorValued
