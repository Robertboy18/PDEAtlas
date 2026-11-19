/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.HighLevels
public import PDE.Elliptic.Regularity.Interior.DeGiorgi.LocalBoundedness
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Normalization

/-!
# The second De Giorgi lemma for the weak equation

A positive measure of the lower half of a solution forces a uniform drop
from its upper bound on a smaller ball. The high-level measure estimate
supplies a small tail after affine normalization; the first De Giorgi lemma
then turns that tail estimate into an almost-everywhere upper bound.

This proves the upper-drop step from the measurable-coefficient weak
equation. The initial state belongs to H¹. The one-sided essential bound is
the normalization used in the oscillation argument.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped NNReal Sobolev ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- A measurable uniformly elliptic weak solution bounded above by one on
the double ball drops below `1 - θ` on the half ball if its nonpositive set
has measure at least `m` on the unit ball. The positive drop is uniform in
the solution and the coefficient matrix within the given bounds. -/
theorem exists_upper_drop_on_half_ball
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α Λ m : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) (hm : 0 < m) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
      ∀ (a : Fin n → Fin n → DerivLp n ∞ (ball (0 : ℝ^n) 2)),
        (∀ i j, ‖a i j‖ ≤ Λ) → AEUniformlyElliptic a α →
      ∀ (u : H¹(ball (0 : ℝ^n) 2)), IsInteriorWeakDivergenceSolution a 0 u →
        (∀ᵐ x ∂volume.restrict (ball (0 : ℝ^n) 2), wkpBaseCoordinateCLM u x ≤ 1) →
        m ≤ (volume.restrict (ball (0 : ℝ^n) 1)).real
          {x | wkpBaseCoordinateCLM u x ≤ 0} →
        ∀ᵐ x ∂volume.restrict (ball (0 : ℝ^n) (1 / 2)),
          wkpBaseCoordinateCLM u x ≤ 1 - θ := by
  obtain ⟨ε, hε, hsmall⟩ := exists_small_tail_threshold_on_balls
    (W := ball (0 : ℝ^n) 2) isBounded_ball hq2 hq hα hΛ
    (r := 1 / 2) (R := 1) (by norm_num) (by norm_num)
  obtain ⟨k, hk, hk1, hlevel⟩ := exists_upper_level_with_small_measure (n := n)
    hα hm (div_pos hε (by norm_num : (0 : ℝ) < 4))
  have hgap : 0 < 1 - k := sub_pos.mpr hk1
  refine ⟨(1 - k) / 2, div_pos hgap (by norm_num), by linarith, ?_⟩
  intro a haΛ ha u hu hupper hlower
  let μ := volume.restrict (ball (0 : ℝ^n) 1)
  let ν := domainMeasure n (ball (0 : ℝ^n) 2)
  let : IsFiniteMeasure ν := isFiniteMeasure_domainMeasure_of_isBounded isBounded_ball
  have h12 : ball (0 : ℝ^n) 1 ⊆ ball 0 2 := ball_subset_ball (by norm_num)
  have hμν : μ ≤ ν := domainMeasure_le h12
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le ν hμν
  let c := 2 / (1 - k)
  have hc : 0 < c := div_pos (by norm_num) hgap
  let v : H¹(ball (0 : ℝ^n) 2) := c • (u - wkpConstant k)
  have hv : IsInteriorWeakDivergenceSolution a 0 v := hu.smul_sub_constant c k
  have hrep : (wkpBaseCoordinateCLM v : ℝ^n → ℝ) =ᵐ[ν]
      fun x ↦ c * (wkpBaseCoordinateCLM u x - k) :=
    wkpBaseCoordinateCLM_smul_sub_constant_ae u c k
  let E := {x | k < wkpBaseCoordinateCLM u x}
  have hE : MeasurableSet E :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable _).measurable
  have ht : (∫ x in ball (0 : ℝ^n) 1,
      max (wkpBaseCoordinateCLM v x - 0) 0 ^ 2) ≤ ε := by
    have hmem : MemLp (wkpBaseCoordinateCLM v) 2 μ := (Lp.memLp _).mono_measure hμν
    calc
      _ ≤ ∫ x, E.indicator (fun _ ↦ (4 : ℝ)) x ∂μ := by
        simp only [sub_zero]
        apply integral_mono_ae hmem.pos_part.integrable_sq
          ((integrable_const (4 : ℝ)).indicator hE)
        filter_upwards [hrep.filter_mono (ae_mono hμν),
          hupper.filter_mono (ae_mono hμν)] with x hx hux
        change max (wkpBaseCoordinateCLM v x) 0 ^ 2 ≤ E.indicator (fun _ ↦ (4 : ℝ)) x
        by_cases hxE : x ∈ E
        · have hvle : wkpBaseCoordinateCLM v x ≤ 2 := by
            rw [hx]
            calc
              _ ≤ c * (1 - k) := mul_le_mul_of_nonneg_left (sub_le_sub_right hux k) hc.le
              _ = 2 := div_mul_cancel₀ 2 hgap.ne'
          rw [indicator_of_mem hxE]
          calc max (wkpBaseCoordinateCLM v x) 0 ^ 2 ≤ 2 ^ 2 :=
              pow_le_pow_left₀ (le_max_right _ _) (max_le hvle zero_le_two) 2
            _ = 4 := by norm_num
        · rw [indicator_of_notMem hxE, hx, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc.le
            (sub_nonpos.mpr (le_of_not_gt hxE)))]
          norm_num
      _ = 4 * μ.real E := by
        rw [integral_indicator hE, integral_const, smul_eq_mul, mul_comm,
          measureReal_restrict_apply_univ]
      _ ≤ ε := by linarith [hlevel a haΛ ha u hu hupper hlower]
  have hvbound := hsmall a haΛ ha v hv 0 h12 0 ht
  have hhalf : volume.restrict (ball (0 : ℝ^n) (1 / 2)) ≤ ν :=
    domainMeasure_le (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 2))
  filter_upwards [hvbound, hrep.filter_mono (ae_mono hhalf)] with x hx heq
  rw [heq] at hx
  simp only [c, zero_add, div_mul_eq_mul_div, div_le_iff₀ hgap] at hx
  linarith

end SobolevSpace.GraphSpace
