/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.UpperDrop
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Normalization

/-!
# Oscillation contraction for measurable elliptic equations

At least half of the unit ball lies on one side of the middle level.
Applying the second De Giorgi lemma to the solution or its negative then
contracts its essential range on the half ball. The contraction factor is
uniform over the weak solutions and coefficient fields with the
given ellipticity bounds.

This is the normalized oscillation step. The first local boundedness theorem
provides a finite essential range for an arbitrary H¹ solution on interior
balls; spatial rescaling and iteration use this contraction.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped NNReal Sobolev ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The essential range of a homogeneous weak solution contracts
from radius one on the double ball to a uniform radius `ρ < 1` on the half
ball. A centre of the smaller interval is supplied together with its bound.
The coefficients need only be essentially bounded and uniformly elliptic. -/
theorem exists_oscillation_contraction_on_half_ball
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ (a : Fin n → Fin n → DerivLp n ∞ (ball (0 : ℝ^n) 2)),
        (∀ i j, ‖a i j‖ ≤ Λ) → AEUniformlyElliptic a α →
      ∀ (u : H¹(ball (0 : ℝ^n) 2)), IsInteriorWeakDivergenceSolution a 0 u →
        (∀ᵐ x ∂volume.restrict (ball (0 : ℝ^n) 2), |wkpBaseCoordinateCLM u x| ≤ 1) →
        ∃ c : ℝ, |c| ≤ 1 - ρ ∧
          ∀ᵐ x ∂volume.restrict (ball (0 : ℝ^n) (1 / 2)),
            |wkpBaseCoordinateCLM u x - c| ≤ ρ := by
  let μ := volume.restrict (ball (0 : ℝ^n) 1)
  let ν := domainMeasure n (ball (0 : ℝ^n) 2)
  let : IsFiniteMeasure ν := isFiniteMeasure_domainMeasure_of_isBounded isBounded_ball
  have hμν : μ ≤ ν := domainMeasure_le (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2))
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le ν hμν
  have hμpos : 0 < μ.real univ := by
    rw [measureReal_restrict_apply_univ]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_lt_top.ne
  obtain ⟨θ, hθ, hθhalf, hdrop⟩ := exists_upper_drop_on_half_ball hq2 hq hα hΛ
    (div_pos hμpos (by norm_num : (0 : ℝ) < 2))
  refine ⟨1 - θ / 2, by linarith, by linarith, ?_⟩
  intro a haΛ ha u hu hnorm
  have hhalf : volume.restrict (ball (0 : ℝ^n) (1 / 2)) ≤ ν :=
    domainMeasure_le (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 2))
  have hnormHalf := hnorm.filter_mono (ae_mono hhalf)
  by_cases hlow : μ.real univ / 2 ≤ μ.real {x | wkpBaseCoordinateCLM u x ≤ 0}
  · have hd := hdrop a haΛ ha u hu (hnorm.mono fun _ hx ↦ (abs_le.mp hx).2) hlow
    refine ⟨-(θ / 2), by rw [abs_neg, abs_of_pos (by positivity)]; linarith, ?_⟩
    filter_upwards [hd, hnormHalf] with x hx hb
    exact abs_le.mpr ⟨by linarith [(abs_le.mp hb).1], by linarith⟩
  · have hcover : μ.real univ ≤
        μ.real {x | wkpBaseCoordinateCLM u x ≤ 0} + μ.real {x | 0 ≤ wkpBaseCoordinateCLM u x} :=
      (measureReal_mono fun x _ ↦ le_total (wkpBaseCoordinateCLM u x) 0).trans
        (measureReal_union_le _ _)
    let v : H¹(ball (0 : ℝ^n) 2) := (-1 : ℝ) • (u - wkpConstant 0)
    have hrep : (wkpBaseCoordinateCLM v : ℝ^n → ℝ) =ᵐ[ν] fun x ↦ -wkpBaseCoordinateCLM u x := by
      simpa only [sub_zero, neg_one_mul] using wkpBaseCoordinateCLM_smul_sub_constant_ae u (-1) 0
    have hvupper : ∀ᵐ x ∂ν, wkpBaseCoordinateCLM v x ≤ 1 := by
      filter_upwards [hrep, hnorm] with x hx hu
      rw [hx]
      linarith [(abs_le.mp hu).1]
    have hvlow : μ.real univ / 2 ≤ μ.real {x | wkpBaseCoordinateCLM v x ≤ 0} := by
      have heq : {x | wkpBaseCoordinateCLM v x ≤ 0} =ᵐ[μ] {x | 0 ≤ wkpBaseCoordinateCLM u x} := by
        filter_upwards [hrep.filter_mono (ae_mono hμν)] with x hx
        rw [hx]
        exact propext neg_nonpos
      rw [measureReal_congr heq]
      linarith [lt_of_not_ge hlow]
    have hd := hdrop a haΛ ha v (hu.smul_sub_constant (-1) 0) hvupper hvlow
    refine ⟨θ / 2, by rw [abs_of_pos (by positivity)]; linarith, ?_⟩
    filter_upwards [hd, hnormHalf, hrep.filter_mono (ae_mono hhalf)] with x hx hb heq
    rw [heq] at hx
    exact abs_le.mpr ⟨by linarith, by linarith [(abs_le.mp hb).2]⟩

end SobolevSpace.GraphSpace
