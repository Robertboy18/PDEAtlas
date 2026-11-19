/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.Chart.Coercivity
public import PDE.Analysis.Operator.StrongMonotonicity.Cutoff
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# A global monotone extension of the chart flux

Two cutoffs have different roles. The larger cutoff `σ` bounds the chart
parameters globally and equals one on the support of `κ`. Blending with `βp`
outside the core of `κ` preserves a positive monotonicity constant even where
the extended chart derivative degenerates.

The constants depend on the chart, cutoffs, and physical flux bounds. Neither
the solution nor the load enters this construction.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open PDE.Analysis.Operator
open scoped NNReal RealInnerProductSpace

variable {n : ℕ}

/-- The chart flux with bounded parameters, blended with a positive linear flux. -/
def extendedChartFlux (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (A : ℝ^n → ℝ^n) (κ σ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (β : ℝ) :
    ℝ^n → ℝ^n → ℝ^n :=
  cutoffFlux κ.toFun
    (fun y ↦ pullbackFlux A (cutoffChartGradientMap E σ y) (cutoffChartJacobian E σ y)) β

/-- Centering the physical flux centers its global chart extension. -/
theorem extendedChartFlux_zero (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (A : ℝ^n → ℝ^n) (hzero : A 0 = 0)
    (κ σ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (β : ℝ) (y : ℝ^n) :
    extendedChartFlux E A κ σ β y 0 = 0 :=
  cutoffFlux_zero _ _ β (pullbackFlux_zero A hzero _ _)

/-- The extension is jointly continuous in the point and gradient variables.
This gives measurability before any regularity of the solution is known. -/
theorem continuous_extendedChartFlux
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 2 (fun y ↦ E.symm y))
    (A : ℝ^n → ℝ^n) (hA : Continuous A)
    (κ σ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (β : ℝ) :
    Continuous (Function.uncurry (extendedChartFlux E A κ σ β)) := by
  have hT := (contDiff_cutoffChartGradientMap E hE
    (hSymm.of_le (by norm_num)) σ).continuous
  have hJ : Continuous (cutoffChartJacobian E σ) := by
    have hd : ContDiff ℝ 1 (fun y ↦ (fderiv ℝ (fun z ↦ E.symm z) y).det) :=
      SobolevSpace.GraphSpace.BoundaryRegularity.contDiff_det_fderiv _ hSymm
    exact (σ.contDiff.continuous.mul hd.continuous).abs
  have hκ := κ.contDiff.continuous
  change Continuous (fun yz : ℝ^n × ℝ^n ↦
    κ.toFun yz.1 • (cutoffChartJacobian E σ yz.1 •
      (cutoffChartGradientMap E σ yz.1).adjoint (A (cutoffChartGradientMap E σ yz.1 yz.2))) +
      (1 - κ.toFun yz.1) • (β • yz.2))
  exact ((hκ.comp continuous_fst).smul ((hJ.comp continuous_fst).smul
    ((ContinuousLinearMap.adjoint.continuous.comp (hT.comp continuous_fst)).clm_apply
      (hA.comp ((hT.comp continuous_fst).clm_apply continuous_snd))))).add
    ((continuous_const.sub (hκ.comp continuous_fst)).smul (continuous_snd.const_smul β))

/-- On the common core of the cutoffs, the extension is the chart flux. -/
theorem extendedChartFlux_eq_of_eq_one
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)) (A : ℝ^n → ℝ^n)
    (κ σ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (β : ℝ)
    {y : ℝ^n} (hκ : κ.toFun y = 1) (hσ : σ.toFun y = 1) (p : ℝ^n) :
    extendedChartFlux E A κ σ β y p = chartFlux E A y p := by
  rw [extendedChartFlux, cutoffFlux_eq_of_eq_one _ _ _ hκ]
  obtain ⟨hT, hJ⟩ := cutoffChartParameters_eq_of_eq_one E σ hσ
  rw [hT, hJ]
  rfl

/-- A centered Lipschitz strongly monotone physical flux has a global chart
extension with positive monotonicity and the joint variation estimate required
by the nonlinear difference-quotient argument. -/
theorem exists_extendedChartFlux_bounds
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 2 (fun y ↦ E.symm y))
    (κ σ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hκ : ∀ y, 0 ≤ κ.toFun y ∧ κ.toFun y ≤ 1)
    (hκtarget : tsupport κ.toFun ⊆ E.target)
    (hσ : ∀ y ∈ tsupport κ.toFun, σ.toFun y = 1)
    (A : ℝ^n → ℝ^n) (hzero : A 0 = 0) {θ : ℝ} (hθ : 0 < θ)
    (hmono : ∀ z w, θ * ‖z - w‖ * ‖z - w‖ ≤ ⟪A z - A w, z - w⟫)
    {C : ℝ≥0} (hLip : LipschitzWith C A) :
    ∃ β : ℝ, 0 < β ∧ ∃ K D : ℝ≥0,
      (∀ y z w, β * ‖z - w‖ * ‖z - w‖ ≤
        ⟪extendedChartFlux E A κ σ β y z - extendedChartFlux E A κ σ β y w, z - w⟫) ∧
      (∀ x y z w,
        ‖extendedChartFlux E A κ σ β y w - extendedChartFlux E A κ σ β x z‖ ≤
          K * ‖y - x‖ * ‖z‖ + D * ‖w - z‖) := by
  obtain ⟨β, hβ, hcoer⟩ := exists_chartFlux_pairing_lower_bound_on_compact
    E (hE.of_le (by norm_num)) (hSymm.of_le (by norm_num))
    κ.hasCompactSupport hκtarget A hθ hmono
  obtain ⟨M, D, hM, hD⟩ := exists_cutoffChartGradientMap_bounds E hE hSymm σ
  obtain ⟨B, H, hB, hH⟩ := exists_cutoffChartJacobian_bounds E hSymm σ
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport κ.hasCompactSupport
    (show ContDiff ℝ 1 κ.toFun from κ.contDiff.of_le (by simp)) (by norm_num)
  let F := fun y ↦ pullbackFlux A
    (cutoffChartGradientMap E σ y) (cutoffChartJacobian E σ y)
  let K₀ : ℝ≥0 := H * C * M ^ 2 + 2 * B * C * M * D
  let C₀ : ℝ≥0 := B * M ^ 2 * C
  let β₀ : ℝ≥0 := ⟨β, hβ.le⟩
  have hstate (x z w : ℝ^n) : ‖F x z - F x w‖ ≤ C₀ * ‖z - w‖ := by
    have h := norm_pullbackFlux_joint_sub_le_of_parameter_bounds A hLip hzero
      (cutoffChartGradientMap E σ) (cutoffChartJacobian E σ) M B D H
      (hM x) (hM x) (hB x) (hB x) (hD x x) (hH x x) w z
    simpa only [F, C₀, sub_self, norm_zero, mul_zero, zero_mul, zero_add,
      NNReal.coe_mul, NNReal.coe_pow] using h
  have hspace (x y z : ℝ^n) : ‖F y z - F x z‖ ≤ K₀ * ‖y - x‖ * ‖z‖ := by
    simpa only [F, K₀, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow,
      NNReal.coe_ofNat] using
      norm_pullbackFlux_sub_le_of_parameter_bounds A hLip hzero
        (cutoffChartGradientMap E σ) (cutoffChartJacobian E σ) M B D H
        (hM x) (hM y) (hB x) (hD y x) (hH y x) z
  refine ⟨β, hβ, K₀ + L * (C₀ + β₀), C₀ + β₀, ?_, ?_⟩
  · intro y z w
    apply cutoffFlux_pairing_lower_bound κ.toFun F (hκ y).1 (hκ y).2 le_rfl
    intro hy v u
    have hyK := subset_tsupport κ.toFun hy
    have hparams := cutoffChartParameters_eq_of_eq_one E σ (hσ y hyK)
    simpa only [F, hparams.1, hparams.2, chartFlux] using hcoer y hyK v u
  · intro x y z w
    have hs := norm_cutoffFlux_state_sub_le κ.toFun F β
      (hκ y).1 (hκ y).2 C₀.coe_nonneg (hstate y) z w
    have hx0 : F x 0 = 0 := pullbackFlux_zero A hzero _ _
    have hκabs : |κ.toFun y| ≤ 1 := by rw [abs_of_nonneg (hκ y).1]; exact (hκ y).2
    have hκdiff : |κ.toFun y - κ.toFun x| ≤ L * ‖y - x‖ := by
      simpa only [Real.norm_eq_abs, TestFunction.toFun_eq_coe] using hL.norm_sub_le y x
    have ht := norm_cutoffFlux_spatial_sub_le κ.toFun F β hκabs hκdiff
      L.coe_nonneg hx0 (hstate x) (hspace x y) z
    have htriangle := norm_sub_le_norm_sub_add_norm_sub
      (cutoffFlux κ.toFun F β y w) (cutoffFlux κ.toFun F β y z)
      (cutoffFlux κ.toFun F β x z)
    simp only [abs_of_pos hβ] at hs ht
    change ‖cutoffFlux κ.toFun F β y w - cutoffFlux κ.toFun F β x z‖ ≤
      ((K₀ : ℝ) + L * ((C₀ : ℝ) + β)) * ‖y - x‖ * ‖z‖ +
        ((C₀ : ℝ) + β) * ‖w - z‖
    exact htriangle.trans ((add_le_add hs ht).trans_eq (add_comm _ _))

end PDE.Elliptic.Regularity.Quasilinear
