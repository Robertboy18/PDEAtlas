/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Generation.Resolvent
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Strong convergence of Yosida approximations

For a densely defined operator satisfying the positive resolvent bounds, `λR_λ` converges
strongly to the identity. The bounded Yosida operators `A_λ = λ(λR_λ - I)` consequently
converge to `A` on its domain.

These are steps 2 and 3 of the proof of Evans §7.4.2, Theorem 4: the definition (18) and the
limits (19) and (20). The spectral parameter ranges over all positive real numbers.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.2, proof of Theorem 4, steps 2-3, (18)-(20),
  pp. 439-440. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Set Topology

namespace PDE.Analysis.Evolution.HasContractionResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : E →ₗ.[ℝ] E} (hA : HasContractionResolvent A)
  {lambda mu : ℝ}

/-- Each scaled positive resolvent is a contraction. -/
theorem norm_smul_resolvent_le (hlambda : 0 < lambda) :
    ‖lambda • hA.resolvent hlambda‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
  calc
    lambda * ‖hA.resolvent hlambda‖ ≤ lambda * lambda⁻¹ :=
      mul_le_mul_of_nonneg_left (hA.norm_resolvent_le hlambda) hlambda.le
    _ = 1 := mul_inv_cancel₀ hlambda.ne'

/-- On the operator domain, the scaled resolvent error decays at rate `λ⁻¹ ‖Ax‖`. -/
theorem norm_smul_resolvent_sub_le (hlambda : 0 < lambda) (x : A.domain) :
    ‖lambda • hA.resolvent hlambda x - (x : E)‖ ≤ lambda⁻¹ * ‖A x‖ := by
  rw [hA.smul_resolvent_sub hlambda x]
  exact hA.norm_resolvent_apply_le hlambda (A x)

/-- The scaled resolvents converge to the identity on the operator domain. -/
theorem tendsto_smul_resolvent_domain (x : A.domain) :
    Tendsto (fun lambda : Ioi (0 : ℝ) ↦
      (lambda : ℝ) • hA.resolvent lambda.property x) atTop (𝓝 (x : E)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun lambda ↦ hA.norm_smul_resolvent_sub_le lambda.property x)
  have hinv : Tendsto (fun lambda : Ioi (0 : ℝ) ↦ (lambda : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_comp_val_Ioi_atTop.mpr tendsto_inv_atTop_zero
  simpa only [zero_mul] using hinv.mul_const ‖A x‖

/-- Density and the uniform contraction bound extend resolvent convergence to every vector. -/
theorem tendsto_smul_resolvent (hdense : Dense (A.domain : Set E)) (x : E) :
    Tendsto (fun lambda : Ioi (0 : ℝ) ↦
      (lambda : ℝ) • hA.resolvent lambda.property x) atTop (𝓝 x) := by
  have hlip (lambda : Ioi (0 : ℝ)) :
      LipschitzWith 1 ((lambda : ℝ) • hA.resolvent lambda.property) :=
    ContinuousLinearMap.lipschitzWith_of_opNorm_le (hA.norm_smul_resolvent_le lambda.property)
  have hequi : Equicontinuous (fun lambda : Ioi (0 : ℝ) ↦
      fun x : E ↦ (lambda : ℝ) • hA.resolvent lambda.property x) :=
    (LipschitzWith.uniformEquicontinuous _ 1 hlip).equicontinuous
  exact (hequi x).tendsto_of_mem_closure continuous_id.continuousWithinAt
    (fun y hy ↦ hA.tendsto_smul_resolvent_domain ⟨y, hy⟩) (hdense x)

/-- The bounded Yosida approximation `A_λ = λ(λR_λ - I)` of the partial operator. -/
def yosidaApproximation (hlambda : 0 < lambda) : E →L[ℝ] E :=
  lambda • (lambda • hA.resolvent hlambda - ContinuousLinearMap.id ℝ E)

/-- Evaluating the Yosida approximation gives its resolvent formula. -/
@[simp]
theorem yosidaApproximation_apply (hlambda : 0 < lambda) (x : E) :
    hA.yosidaApproximation hlambda x =
      lambda • (lambda • hA.resolvent hlambda x - x) :=
  rfl

/-- On the original domain the bounded approximation equals `λR_λAx`. -/
theorem yosidaApproximation_domain (hlambda : 0 < lambda) (x : A.domain) :
    hA.yosidaApproximation hlambda x = lambda • hA.resolvent hlambda (A x) := by
  rw [hA.yosidaApproximation_apply, hA.smul_resolvent_sub hlambda x]

/-- The Yosida approximations converge to the original operator on its domain. -/
theorem tendsto_yosidaApproximation (hdense : Dense (A.domain : Set E)) (x : A.domain) :
    Tendsto (fun lambda : Ioi (0 : ℝ) ↦ hA.yosidaApproximation lambda.property x)
      atTop (𝓝 (A x)) := by
  exact (hA.tendsto_smul_resolvent hdense (A x)).congr fun lambda ↦
    (hA.yosidaApproximation_domain lambda.property x).symm

/-- The bounded Yosida approximations commute at any two positive parameters. -/
theorem yosidaApproximation_commute (hlambda : 0 < lambda) (hmu : 0 < mu) :
    Commute (hA.yosidaApproximation hlambda) (hA.yosidaApproximation hmu) := by
  change Commute (lambda • (lambda • hA.resolvent hlambda - 1))
    (mu • (mu • hA.resolvent hmu - 1))
  exact (((((hA.resolvent_commute hlambda hmu).smul_left lambda).smul_right mu).sub_left
    (Commute.one_left _)).sub_right (Commute.one_right _)).smul_left lambda |>.smul_right mu

end PDE.Analysis.Evolution.HasContractionResolvent
