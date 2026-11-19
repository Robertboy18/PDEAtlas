/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.FixedPoint
public import PDE.Fluid.DeGregorio.Uniqueness.Interior

/-!
# Coupled uniqueness with L² endpoint traces

The coupled energy inequality requires only spatial derivatives of the velocity.
An interior classical solution with continuous L² traces is therefore unique in
the supported H² class on its whole interval, for every interval length.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution PDE.Common
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

open DeGregorio

variable {B : NNReal} {T R : ℝ} {hT : 0 ≤ T}
  {F G : C(Icc (0 : ℝ) T,
    supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
  {W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))} {w₀ : ℝ → ℝ} {c d w z : ℝ → ℝ → ℝ}

/-- Two coupled outputs with the same datum agree on the whole time interval.
The interval length and the common H² bound are arbitrary. -/
theorem IsHkFrozenOutput.eq_of_self
    (hF : IsHkFrozenOutput hT F F W₀ w₀ c w)
    (hG : IsHkFrozenOutput hT G G W₀ w₀ d z) : F = G := by
  let L := max R 0 + 1
  have hL : 0 ≤ L := (le_max_right R 0).trans (le_add_of_nonneg_right zero_le_one)
  have hRL : R < L := (le_max_left R 0).trans_lt (lt_add_one _)
  let fields : Fields := ⟨w, hkCurveHilbertVelocity hT F⟩
  let other : Fields := ⟨z, hkCurveHilbertVelocity hT G⟩
  have htrace : ContinuousOn (differenceEnergy fields other L) (Icc 0 T) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (Icc (0 : ℝ) T).domRestrict (differenceEnergy fields other L) =
        fun s ↦ dist (F s) (G s) ^ 2 := by
      funext s
      exact hF.differenceEnergy_eq_dist_sq hG hRL.le s
    rw [heq]
    exact (F.continuous.dist G.continuous).pow 2
  have hinitial : differenceEnergy fields other L 0 = 0 := by
    simp only [differenceEnergy, fields, other, hF.initial, hG.initial, sub_self,
      zero_pow (by norm_num : 2 ≠ 0), integral_zero]
  have henergy := differenceEnergy_eq_zero_of_same_initialData_interior
    (fields := fields) (other := other) hF.classical hG.classical
    (fun t _ ↦ hF.contDiff_velocity t) (fun t _ ↦ hG.contDiff_velocity t)
    hF.isClassicalSolutionOn hG.isClassicalSolutionOn hL
    (by positivity : 0 ≤ 2 * (B : ℝ)) (by
      intro t ht x hx
      have hRx : R < |x| := hRL.trans_le (le_of_not_gt fun h ↦ hx (abs_lt.mp h))
      exact ⟨hF.support x t (Ioo_subset_Icc_self ht) hRx,
        hG.support x t (Ioo_subset_Icc_self ht) hRx⟩) (by
      intro t _
      simp only [fields, other, hkCurveHilbertVelocity, l2Primitive,
        intervalIntegral.integral_same]) (by
      intro t ht x _
      have hb := hG.spatial_bounds ⟨t, Ioo_subset_Icc_self ht⟩ x
      change |deriv (fun y ↦ hkCurveHilbertVelocity hT F y t) x| ≤ _ ∧ _
      rw [(hF.velocity_derivative x t).deriv]
      exact ⟨hF.coefficient_bound x t, hb⟩) htrace hinitial
  apply ContinuousMap.ext
  intro t
  apply dist_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [← hF.differenceEnergy_eq_dist_sq hG hRL.le t]
  exact henergy t t.property

/-- Equality of the coupled L² curves also gives pointwise equality of their
continuous vorticity representatives and the normalized velocities. -/
theorem IsHkFrozenOutput.fields_eq_of_self
    (hF : IsHkFrozenOutput hT F F W₀ w₀ c w)
    (hG : IsHkFrozenOutput hT G G W₀ w₀ d z) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      w x t = z x t ∧ hkCurveHilbertVelocity hT F x t = hkCurveHilbertVelocity hT G x t := by
  have hFG := hF.eq_of_self hG
  subst G
  intro t ht x
  have hae := (hF.representative ⟨t, ht⟩).symm.trans (hG.representative ⟨t, ht⟩)
  have hcF : Continuous (fun y ↦ w y t) :=
    hF.continuous.comp
      (continuous_id.prodMk (continuous_const (y := (⟨t, ht⟩ : Icc (0 : ℝ) T))))
  have hcG : Continuous (fun y ↦ z y t) :=
    hG.continuous.comp
      (continuous_id.prodMk (continuous_const (y := (⟨t, ht⟩ : Icc (0 : ℝ) T))))
  have heq := (Continuous.ae_eq_iff_eq volume hcF hcG).mp hae
  exact ⟨congrFun heq x, rfl⟩

end DeGregorio.Iteration
