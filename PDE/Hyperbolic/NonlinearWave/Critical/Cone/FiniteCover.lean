/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Common.Euclidean.SpaceTime
import PDE.Analysis.MeasureTheory.Lp.Continuous
import PDE.Analysis.MeasureTheory.Lp.FiniteSupportCover

/-!
# From enlarged cones to a whole-space critical tail

Each enlarged cone contains a fixed spatial ball. Compactness supplies a finite cover and a common
late time, so local critical mixed norms give a whole-space tail. Speed-one support supplies the
compact container without a terminal slice.

This is step 6 of the proof of Evans, §12.4, Theorem 3: finitely many balls `B(x_k, δ(x_k))` cover
the support, and (22) gives the critical mixed norm on a late time interval.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 3, step 6 of its proof, equation (22).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- An enlarged cone controls its fixed inner ball until the original endpoint. -/
theorem memLp_four_twelve_inner_ball_of_enlarged_cone {u : ℝ^4 → ℝ} {T s δ : ℝ}
    (hu : ContinuousOn u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : 0 < s)
    (hcone : MemLp (fun t ↦ lpNorm (fun x ↦ u (timeSpaceCons t x)) 12
      (volume.restrict (Metric.ball c (T + δ - t)))) 4 (volume.restrict (Ico s T))) :
    MemLp (fun t ↦ lpNorm (fun x ↦ u (timeSpaceCons t x)) 12 (volume.restrict (Metric.ball c δ))) 4
      (volume.restrict (Ico s T)) := by
  classical
  let v : ℝ^4 → ℝ := {p | 0 < p 0 ∧ p 0 < T}.indicator u
  have hb : MeasurableSet {p : ℝ^4 | 0 < p 0 ∧ p 0 < T} :=
    ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)).measurableSet
  have hv : Measurable v := by
    simpa only [v, piecewise_eq_indicator] using
      hu.measurable_piecewise continuous_zero.continuousOn hb
  have hc : Continuous (fun q : ℝ × ℝ^3 ↦ timeSpaceCons q.1 q.2) :=
    (timeSpaceContinuousLinearEquiv 3).symm.continuous
  have hm : Measurable (fun t ↦ lpNorm (fun x ↦ v (timeSpaceCons t x)) 12
      (volume.restrict (Metric.ball c δ))) := ((hv.comp hc.measurable).eLpNorm_prod_right
      (by norm_num) (by norm_num)).ennreal_toReal
  have he (t : ℝ) (ht : t ∈ Ico s T) :
      (fun x ↦ v (timeSpaceCons t x)) = fun x ↦ u (timeSpaceCons t x) := by
    funext x
    exact indicator_of_mem (by simpa using And.intro (hs.trans_le ht.1) ht.2) u
  have hsmall : MemLp (fun t ↦ lpNorm (fun x ↦ v (timeSpaceCons t x)) 12
      (volume.restrict (Metric.ball c δ))) 4 (volume.restrict (Ico s T)) := by
    apply hcone.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    rw [Real.norm_of_nonneg lpNorm_nonneg, he t ht]
    have hmem : MemLp (fun x ↦ u (timeSpaceCons t x)) 12
        (volume.restrict (Metric.ball c (T + δ - t))) := by
      apply ContinuousOn.memLp_of_subset_isCompact
        (s := Metric.closedBall c (T + δ - t)) ?_ (isCompact_closedBall _ _)
        measurableSet_ball Metric.ball_subset_closedBall
      exact hu.comp (hc.comp (continuous_const.prodMk continuous_id)).continuousOn
        (fun x _ ↦ by simpa using And.intro (hs.trans_le ht.1) ht.2)
    exact ENNReal.toReal_mono hmem.eLpNorm_ne_top (eLpNorm_mono_measure _
      (Measure.restrict_mono (Metric.ball_subset_ball (by linarith [ht.2])) le_rfl))
  apply MemLp.ae_eq ?_ hsmall
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  rw [he t ht]

/-- Critical norms on enlarged cones give a global critical tail when the
slices stay in a common compact spatial set. No terminal slice is required. -/
theorem exists_memLp_four_twelve_of_compact_support_and_enlarged_cones {u : ℝ^4 → ℝ} {T : ℝ}
    (hT : 0 < T) (hu : ContinuousOn u {p | 0 < p 0 ∧ p 0 < T}) {K : Set (ℝ^3)} (hK : IsCompact K)
    (hsupport : ∀ t ∈ Ioo 0 T, Function.support (fun x ↦ u (timeSpaceCons t x)) ⊆ K)
    (hcone : ∀ c ∈ K, ∃ s ∈ Ioo 0 T, ∃ δ > 0, MemLp (fun t ↦
      lpNorm (fun x ↦ u (timeSpaceCons t x)) 12 (volume.restrict (Metric.ball c (T + δ - t)))) 4
      (volume.restrict (Ico s T))) :
    ∃ s ∈ Ioo 0 T, MemLp (fun t ↦ lpNorm (fun x ↦ u (timeSpaceCons t x)) 12 volume) 4
      (volume.restrict (Ico s T)) := by
  classical
  choose start hstart radius hradius hnorm using (fun c : K ↦ hcone c c.property)
  obtain ⟨a, ha⟩ := hK.elim_finite_subcover (fun c : K ↦ Metric.ball c (radius c))
    (fun _ ↦ Metric.isOpen_ball) (fun x hx ↦ mem_iUnion.mpr
      ⟨⟨x, hx⟩, Metric.mem_ball_self (hradius ⟨x, hx⟩)⟩)
  have hlate : ∀ᶠ s in 𝓝[<] T, ∀ c ∈ a, start c < s := by
    apply (eventually_all_finset a).mpr
    intro c _
    have ht : ∀ᶠ r in 𝓝[<] T, r ∈ Ioo (start c) T := Ioo_mem_nhdsLT (hstart c).2
    exact ht.mono fun _ hr ↦ hr.1
  have htimes : ∀ᶠ s in 𝓝[<] T, s ∈ Ioo 0 T := Ioo_mem_nhdsLT hT
  obtain ⟨s, hs, hstarts⟩ := (htimes.and hlate).exists
  let v : ℝ^4 → ℝ := {p | 0 < p 0 ∧ p 0 < T}.indicator u
  have hb : MeasurableSet {p : ℝ^4 | 0 < p 0 ∧ p 0 < T} :=
    ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)).measurableSet
  have hv : Measurable v := by
    simpa only [v, piecewise_eq_indicator] using
      hu.measurable_piecewise continuous_zero.continuousOn hb
  have hc : Continuous (fun q : ℝ × ℝ^3 ↦ timeSpaceCons q.1 q.2) :=
    (timeSpaceContinuousLinearEquiv 3).symm.continuous
  have he (t : ℝ) (ht : t ∈ Ico s T) :
      (fun x ↦ v (timeSpaceCons t x)) = fun x ↦ u (timeSpaceCons t x) := by
    funext x
    exact indicator_of_mem (by simpa using And.intro (hs.1.trans_le ht.1) ht.2) u
  have hmem : MemLp (fun t ↦ lpNorm (fun x ↦ v (timeSpaceCons t x)) 12 volume)
      4 (volume.restrict (Ico s T)) := by
    apply memLp_lpNorm_of_finite_support_cover (hv.comp hc.measurable)
      (by norm_num) (by norm_num) a (fun c : K ↦ Metric.ball c (radius c))
      (fun _ _ ↦ measurableSet_ball)
    · filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      intro c _
      dsimp only [Function.comp_def]
      rw [he t ht]
      apply ContinuousOn.memLp_of_subset_isCompact
        (s := Metric.closedBall (c : ℝ^3) (radius c)) ?_ (isCompact_closedBall _ _)
        measurableSet_ball Metric.ball_subset_closedBall
      exact hu.comp (hc.comp (continuous_const.prodMk continuous_id)).continuousOn
        (fun x _ ↦ by simpa using And.intro (hs.1.trans_le ht.1) ht.2)
    · filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      dsimp only [Function.comp_def]
      rw [he t ht]
      exact (hsupport t ⟨hs.1.trans_le ht.1, ht.2⟩).trans ha
    · intro c hca
      have hinner := memLp_four_twelve_inner_ball_of_enlarged_cone hu (c : ℝ^3)
        (hstart c).1 (hnorm c)
      have hsub : Ico s T ⊆ Ico (start c) T := fun _ ht ↦ ⟨(hstarts c hca).le.trans ht.1, ht.2⟩
      apply MemLp.ae_eq ?_ (hinner.mono_measure (Measure.restrict_mono hsub le_rfl))
      filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      dsimp only [Function.comp_def]
      rw [he t ht]
  refine ⟨s, hs, MemLp.ae_eq ?_ hmem⟩
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  rw [he t ht]

/-- Speed-one support supplies the common compact container for the
finite-cover argument, without assigning a value to the terminal slice. -/
theorem exists_memLp_four_twelve_of_forward_support_and_enlarged_cones {u : ℝ^4 → ℝ} {T R : ℝ}
    (hT : 0 < T) (hu : ContinuousOn u {p | 0 < p 0 ∧ p 0 < T})
    (hsupport : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, R + t < ‖x‖ → u (timeSpaceCons t x) = 0)
    (hcone : ∀ c : ℝ^3, ∃ s ∈ Ioo 0 T, ∃ δ > 0, MemLp (fun t ↦
      lpNorm (fun x ↦ u (timeSpaceCons t x)) 12 (volume.restrict (Metric.ball c (T + δ - t)))) 4
      (volume.restrict (Ico s T))) :
    ∃ s ∈ Ioo 0 T, MemLp (fun t ↦ lpNorm (fun x ↦ u (timeSpaceCons t x)) 12 volume) 4
      (volume.restrict (Ico s T)) := by
  apply exists_memLp_four_twelve_of_compact_support_and_enlarged_cones hT hu
    (isCompact_closedBall (0 : ℝ^3) (R + T)) ?_ (fun c _ ↦ hcone c)
  intro t ht x hx
  by_contra hnot
  have hxR : R + T < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hnot
  exact hx (hsupport t ht x (by linarith [ht.2]))

end WaveEquation.Critical
