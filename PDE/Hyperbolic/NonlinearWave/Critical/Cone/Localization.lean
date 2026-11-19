/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.SpaceTime
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import PDE.Analysis.MeasureTheory.Lp.Continuous
import PDE.Analysis.MeasureTheory.Lp.SectionNorm
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Measurable localization to a backward cone

The indicator of a backward cone inside the positive-time band gives a jointly measurable
field on fixed spatial volume. Its section norms and mixed norms agree with restriction of the
original field to the moving balls. Continuity on the open time band supplies
spatial Lp membership and local critical mixed integrability, without terminal
regularity or a support hypothesis.

The indicator is used only for measure-theoretic localization; it is never
differentiated or treated as a solution of the wave equation.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- Zero extension from the moving cone inside the open forward time band. -/
def movingConeField (u : ℝ^4 → ℝ) (c : ℝ^3) (T : ℝ) : ℝ × ℝ^3 → ℝ :=
  {q | 0 < q.1 ∧ q.1 < T ∧ dist q.2 c < T - q.1}.indicator
    (fun q ↦ u (timeSpaceCons q.1 q.2))

/-- Continuity only on the open forward band gives a globally measurable cone mask. -/
theorem measurable_movingConeField {u : ℝ^4 → ℝ} {T : ℝ}
    (hu : ContinuousOn u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) :
    Measurable (movingConeField u c T) := by
  classical
  have hc : Continuous (fun q : ℝ × ℝ^3 ↦ timeSpaceCons q.1 q.2) :=
    (timeSpaceContinuousLinearEquiv 3).symm.continuous
  have hs : MeasurableSet {q : ℝ × ℝ^3 | 0 < q.1 ∧ q.1 < T ∧ dist q.2 c < T - q.1} :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_fst continuous_const).measurableSet.inter
        (isOpen_lt (continuous_snd.dist continuous_const)
          (continuous_const.sub continuous_fst)).measurableSet)
  have hf : ContinuousOn (fun q : ℝ × ℝ^3 ↦ u (timeSpaceCons q.1 q.2))
      {q | 0 < q.1 ∧ q.1 < T ∧ dist q.2 c < T - q.1} :=
    hu.comp hc.continuousOn (fun q hq ↦ by simpa using And.intro hq.1 hq.2.1)
  simpa only [movingConeField, piecewise_eq_indicator] using
    hf.measurable_piecewise continuous_zero.continuousOn hs

/-- A physical time section is the usual open-ball indicator. -/
theorem movingConeField_section {u : ℝ^4 → ℝ} {c : ℝ^3} {T t : ℝ} (ht : t ∈ Ioo 0 T) :
    (fun x ↦ movingConeField u c T (t, x)) = (Metric.ball c (T - t)).indicator
      (fun x ↦ u (timeSpaceCons t x)) := by
  classical
  funext x
  simp [movingConeField, indicator, ht.1, ht.2, Metric.mem_ball]

/-- Every extended spatial norm agrees exactly with restriction to the moving ball. -/
theorem eLpNorm_movingConeField {u : ℝ^4 → ℝ} {c : ℝ^3} {T t : ℝ} (ht : t ∈ Ioo 0 T) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ movingConeField u c T (t, x)) p volume =
      eLpNorm (fun x ↦ u (timeSpaceCons t x)) p (volume.restrict (Metric.ball c (T - t))) := by
  rw [movingConeField_section ht,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.nullMeasurableSet]

/-- The real spatial norm has the same exact restriction formula. -/
theorem lpNorm_movingConeField {u : ℝ^4 → ℝ} {c : ℝ^3} {T t : ℝ} (ht : t ∈ Ioo 0 T) (p : ℝ≥0∞) :
    lpNorm (fun x ↦ movingConeField u c T (t, x)) p volume =
      lpNorm (fun x ↦ u (timeSpaceCons t x)) p (volume.restrict (Metric.ball c (T - t))) :=
  congrArg ENNReal.toReal (eLpNorm_movingConeField ht p)

/-- Each physical section belongs to every spatial Lp space by compact-ball continuity. -/
theorem memLp_movingConeField {u : ℝ^4 → ℝ} {T t : ℝ} (hu : ContinuousOn u {p | 0 < p 0 ∧ p 0 < T})
    (c : ℝ^3) (ht : t ∈ Ioo 0 T) (p : ℝ≥0∞) :
    MemLp (fun x ↦ movingConeField u c T (t, x)) p volume := by
  rw [movingConeField_section ht, memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet]
  apply ContinuousOn.memLp_of_subset_isCompact (s := Metric.closedBall c (T - t))
    ?_ (isCompact_closedBall _ _) measurableSet_ball Metric.ball_subset_closedBall
  have hc : Continuous (fun x : ℝ^3 ↦ timeSpaceCons t x) :=
    (timeSpaceContinuousLinearEquiv 3).symm.continuous.comp (continuous_const.prodMk continuous_id)
  exact hu.comp hc.continuousOn (fun x _ ↦ by simpa using ht)

/-- Every compact preterminal time interval has finite critical mixed norm. -/
theorem memLp_four_twelve_movingConeField_local {u : ℝ^4 → ℝ} {T s t : ℝ}
    (hu : ContinuousOn u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : 0 < s) (ht : t < T) :
    MemLp (fun r ↦ lpNorm (fun x ↦ movingConeField u c T (r, x)) 12 volume) 4
      (volume.restrict (Icc s t)) := by
  classical
  let D : Set (ℝ × ℝ^3) := Icc s t ×ˢ Metric.closedBall c (T - s)
  have hD : IsCompact D := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hc : Continuous (fun q : ℝ × ℝ^3 ↦ timeSpaceCons q.1 q.2) :=
    (timeSpaceContinuousLinearEquiv 3).symm.continuous
  have hcont : ContinuousOn (fun q : ℝ × ℝ^3 ↦ u (timeSpaceCons q.1 q.2)) D :=
    hu.comp hc.continuousOn (fun q hq ↦ by
      simpa using And.intro (hs.trans_le hq.1.1) (hq.1.2.trans_lt ht))
  obtain ⟨B, hB⟩ := hD.exists_bound_of_continuousOn hcont
  let g : ℝ^3 → ℝ := (Metric.closedBall c (T - s)).indicator (fun _ ↦ max B 0)
  have hg : MemLp g 12 volume := by
    apply (memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet).2
    exact continuous_const.continuousOn.memLp_of_subset_isCompact
      (isCompact_closedBall _ _) measurableSet_closedBall Subset.rfl
  have hmeas : Measurable (fun r ↦ lpNorm (fun x ↦ movingConeField u c T (r, x)) 12 volume) :=
    ((measurable_movingConeField hu c).eLpNorm_prod_right
      (by norm_num) (by norm_num)).ennreal_toReal
  apply MemLp.of_bound hmeas.aestronglyMeasurable (lpNorm g 12 volume)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  rw [Real.norm_of_nonneg lpNorm_nonneg]
  apply lpNorm_mono_real hg
  intro x
  rw [congrFun (movingConeField_section (u := u) (c := c) ⟨hs.trans_le hr.1, hr.2.trans_lt ht⟩) x]
  by_cases hx : x ∈ Metric.ball c (T - r)
  · have hx' : x ∈ Metric.closedBall c (T - s) :=
      Metric.ball_subset_closedBall ((Metric.ball_subset_ball (sub_le_sub_left hr.1 T)) hx)
    rw [indicator_of_mem hx, show g x = max B 0 from indicator_of_mem hx' _]
    exact (hB (r, x) ⟨hr, hx'⟩).trans (le_max_left _ _)
  · rw [indicator_of_notMem hx, norm_zero]
    exact indicator_nonneg (fun _ _ ↦ le_max_right B 0) x

/-- Moving spatial restrictions are exactly fixed-volume norms of the jointly measurable field. -/
theorem mixed_eLpNorm_movingConeField {u : ℝ^4 → ℝ} {c : ℝ^3} {T : ℝ} {J : Set ℝ} (hJ : J ⊆ Ioo 0 T)
    (hJm : MeasurableSet J) (p q : ℝ≥0∞) :
    eLpNorm (fun t ↦ eLpNorm (fun x ↦ movingConeField u c T (t, x)) p volume) q
      (volume.restrict J) = eLpNorm (fun t ↦ eLpNorm (fun x ↦ u (timeSpaceCons t x)) p
      (volume.restrict (Metric.ball c (T - t)))) q (volume.restrict J) := by
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hJm] with t ht
  exact eLpNorm_movingConeField (hJ ht) p

/-- The corresponding identity for the real section norms used by the bootstrap. -/
theorem mixed_lpNorm_movingConeField {u : ℝ^4 → ℝ} {c : ℝ^3} {T : ℝ} {J : Set ℝ} (hJ : J ⊆ Ioo 0 T)
    (hJm : MeasurableSet J) (p q : ℝ≥0∞) :
    lpNorm (fun t ↦ lpNorm (fun x ↦ movingConeField u c T (t, x)) p volume) q (volume.restrict J) =
      lpNorm (fun t ↦ lpNorm (fun x ↦ u (timeSpaceCons t x)) p
      (volume.restrict (Metric.ball c (T - t)))) q (volume.restrict J) := by
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hJm] with t ht
  exact lpNorm_movingConeField (hJ ht) p

/-- Membership also transfers; the identity of totalized real norms alone would not suffice. -/
theorem mixed_memLp_movingConeField_iff {u : ℝ^4 → ℝ} {c : ℝ^3} {T : ℝ} {J : Set ℝ}
    (hJ : J ⊆ Ioo 0 T) (hJm : MeasurableSet J) (p q : ℝ≥0∞) :
    MemLp (fun t ↦ lpNorm (fun x ↦ movingConeField u c T (t, x)) p volume) q (volume.restrict J) ↔
      MemLp (fun t ↦ lpNorm (fun x ↦ u (timeSpaceCons t x)) p
      (volume.restrict (Metric.ball c (T - t)))) q (volume.restrict J) := by
  apply memLp_congr_ae
  filter_upwards [ae_restrict_mem hJm] with t ht
  exact lpNorm_movingConeField (hJ ht) p

/-- The fixed-volume forcing is exactly the localized physical quintic forcing. -/
theorem lpNorm_quintic_movingConeField {u : ℝ^4 → ℝ} {c : ℝ^3} {T t : ℝ} (ht : t ∈ Ioo 0 T) :
    lpNorm (fun x ↦ movingConeField u c T (t, x) ^ 5) 2 volume =
      lpNorm (fun x ↦ u (timeSpaceCons t x) ^ 5) 2 (volume.restrict (Metric.ball c (T - t))) := by
  classical
  have he : (fun x ↦ movingConeField u c T (t, x) ^ 5) =
      (Metric.ball c (T - t)).indicator (fun x ↦ u (timeSpaceCons t x) ^ 5) := by
    funext x
    have hx := congrFun (movingConeField_section (u := u) (c := c) ht) x
    rw [hx]
    by_cases hx' : x ∈ Metric.ball c (T - t) <;> simp [hx']
  rw [he]
  exact congrArg ENNReal.toReal
    (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.nullMeasurableSet)

end WaveEquation.Critical
