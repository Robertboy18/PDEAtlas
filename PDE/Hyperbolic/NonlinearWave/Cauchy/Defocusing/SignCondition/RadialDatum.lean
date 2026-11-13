/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.Potential
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Spaces
public import PDE.Spaces.Sobolev.Calculus.RadialPower
import CAS.IntegrationTactic

/-!
# A singular finite-energy datum for the seventh-power wave reaction

The radial function `max (‖x‖^(-1/3) - 1) 0` in three dimensions has an
`H¹` representative and integrable eighth-power potential. The totalized
real power selects value zero at the origin; that value is irrelevant to the
Sobolev and integral assertions.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev
open PDE.Analysis (primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- A compactly supported radial singularity, with value zero at the origin. -/
def singularRadialDatum (x : ℝ^3) : ℝ := max (‖x‖ ^ (-(1 / 3 : ℝ)) - 1) 0

/-- The datum is nonnegative at every point. -/
theorem singularRadialDatum_nonneg (x : ℝ^3) : 0 ≤ singularRadialDatum x :=
  le_max_right _ _

/-- The totalized representative takes value zero at the origin. -/
@[simp] theorem singularRadialDatum_zero : singularRadialDatum 0 = 0 := by
  norm_num [singularRadialDatum, Real.zero_rpow]

/-- The datum is zero outside the unit ball. -/
theorem singularRadialDatum_eq_zero_of_one_le_norm {x : ℝ^3} (hx : 1 ≤ ‖x‖) :
    singularRadialDatum x = 0 :=
  max_eq_right (sub_nonpos.mpr
    (Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)))

/-- The singular representative is compactly supported despite being unbounded. -/
theorem hasCompactSupport_singularRadialDatum : HasCompactSupport singularRadialDatum := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^3) 1) ?_
  intro x hx
  apply singularRadialDatum_eq_zero_of_one_le_norm
  have h : ¬ ‖x‖ ≤ 1 := by simpa using hx
  exact (lt_of_not_ge h).le

/-- Its weak derivative is constructed through removable-point differentiation. -/
theorem exists_h1_singularRadialDatum :
    ∃ G : H¹(ℝ^3), baseRepresentative G =ᵐ[volume] singularRadialDatum := by
  obtain ⟨G, hG⟩ := exists_w1p_posPart_norm_rpow_sub_one (n := 2) (p := 2) (a := -(1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨G, hG⟩

/-- The eighth power is below the dimensional integrability threshold. -/
theorem memLp_singularRadialDatum_eight : MemLp singularRadialDatum 8 volume :=
  memLp_posPart_norm_rpow_sub_one (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- The normalized eighth-power potential is integrable. -/
theorem integrable_singularRadialDatum_potential :
    Integrable (fun x ↦ singularRadialDatum x ^ 8 / 8) volume := by
  have h := memLp_singularRadialDatum_eight.integrable_norm_pow (p := 8) (by decide)
  have hpow : Integrable (fun x ↦ singularRadialDatum x ^ 8) volume := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (singularRadialDatum_nonneg _)] using h
  exact hpow.div_const 8

/-- The scalar potential of the seventh-power reaction. -/
theorem potential_pow_seven (z : ℝ) : primitive (fun s ↦ s ^ 7) z = z ^ 8 / 8 := by
  unfold primitive
  cas

/-- The radial datum satisfies the initial-displacement and potential hypotheses of the
sign-condition energy space. -/
theorem exists_energyDatum_singularRadialDatum :
    ∃ G : H¹(ℝ^3), ((energyTriple 3).inclusion G : ℝ^3 → ℝ) =ᵐ[volume] singularRadialDatum ∧
      Integrable (fun x ↦ primitive (fun s ↦ s ^ 7) ((energyTriple 3).inclusion G x))
        (domainMeasure 3 univ) := by
  obtain ⟨G, hG⟩ := exists_h1_singularRadialDatum
  have hinc : ((energyTriple 3).inclusion G : ℝ^3 → ℝ) =ᵐ[volume] singularRadialDatum := hG
  refine ⟨G, hinc, ?_⟩
  simp only [domainMeasure, Measure.restrict_univ]
  apply integrable_singularRadialDatum_potential.congr
  filter_upwards [hinc] with x hx
  rw [potential_pow_seven, hx]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
