/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.GradientRescaling
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Area.Rescaling

/-!
# Pointwise rescaling of the paired gradient in an actual boundary chart

Both offset gradients use the canonical fundamental solution. The actual tangent
map is orthogonal to the intrinsic normal, so their tangential components cancel
in the limit. The remaining density is the tangent Poisson density multiplied by
the actual chart Jacobian, without an isometry assumption on the chart.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open Filter Set PDE.Analysis PotentialTheory
open scoped Gradient Topology

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The two tangent-plane gradient values give the positively oriented Poisson density. -/
theorem sub_gradient_fundamentalSolution_tangent (hm : 1 ≤ m)
    (i : Fin hΩ.N) {a : ℝ^m} (ha : a ∈ chartBoundaryParameterDomain (Ω := Ω) i)
    (x : frontier Ω) (hx : chartBoundaryParametrization (Ω := Ω) i a = (x : ℝ^(m + 1)))
    (v : ℝ^m) :
    ∇ (fundamentalSolution (m + 1))
        (-outwardUnitNormal (Ω := Ω) x - chartBoundaryTangentialDerivative i a v) -
      ∇ (fundamentalSolution (m + 1))
        (outwardUnitNormal (Ω := Ω) x - chartBoundaryTangentialDerivative i a v) =
      (2 / (unitSphereArea (m + 1) *
        ‖outwardUnitNormal (Ω := Ω) x - chartBoundaryTangentialDerivative i a v‖ ^
          (m + 1))) • outwardUnitNormal (Ω := Ω) x := by
  have hminus := normal_sub_chartBoundaryTangentialDerivative_ne_zero i ha x hx
    (s := (-1 : ℝ)) (by norm_num) v
  have hplus := normal_sub_chartBoundaryTangentialDerivative_ne_zero i ha x hx
    (s := (1 : ℝ)) one_ne_zero v
  simp only [neg_one_smul, one_smul] at hminus hplus
  have hnorm :
      ‖-outwardUnitNormal (Ω := Ω) x - chartBoundaryTangentialDerivative i a v‖ =
        ‖outwardUnitNormal (Ω := Ω) x - chartBoundaryTangentialDerivative i a v‖ := by
    have hm := norm_normal_sub_chartBoundaryTangentialDerivative_sq i ha x hx (-1) v
    have hp := norm_normal_sub_chartBoundaryTangentialDerivative_sq i ha x hx 1 v
    simp only [neg_one_smul, one_smul, neg_sq, one_pow] at hm hp
    nlinarith [norm_nonneg
      (-outwardUnitNormal (Ω := Ω) x - chartBoundaryTangentialDerivative i a v),
      norm_nonneg (outwardUnitNormal (Ω := Ω) x - chartBoundaryTangentialDerivative i a v)]
  rw [gradient_fundamentalSolution (by omega) hminus,
    gradient_fundamentalSolution (by omega) hplus, hnorm, ← smul_sub]
  have hvec : -outwardUnitNormal (Ω := Ω) x - chartBoundaryTangentialDerivative i a v -
      (outwardUnitNormal (Ω := Ω) x - chartBoundaryTangentialDerivative i a v) =
        (-2 : ℝ) • outwardUnitNormal (Ω := Ω) x := by
    rw [neg_smul, two_smul]
    abel
  rw [hvec, smul_smul]
  congr 1
  ring

/-- The actual rescaled Jacobian-weighted paired gradient tends to its tangent Poisson density. -/
theorem tendsto_chartBoundary_paired_gradient_rescale (hm : 1 ≤ m)
    (i : Fin hΩ.N) {a : ℝ^m} (ha : a ∈ chartBoundaryParameterDomain (Ω := Ω) i)
    (x : frontier Ω) (hx : chartBoundaryParametrization (Ω := Ω) i a = (x : ℝ^(m + 1)))
    (v : ℝ^m) :
    Tendsto (fun t : ℝ ↦ chartBoundaryJacobian (Ω := Ω) i (a + t • v) •
      (t ^ m • (∇ (fundamentalSolution (m + 1))
          ((x : ℝ^(m + 1)) - t • outwardUnitNormal (Ω := Ω) x -
            chartBoundaryParametrization i (a + t • v)) -
        ∇ (fundamentalSolution (m + 1))
          ((x : ℝ^(m + 1)) + t • outwardUnitNormal (Ω := Ω) x -
            chartBoundaryParametrization i (a + t • v)))))
      (𝓝[>] 0)
      (𝓝 ((chartBoundaryJacobian (Ω := Ω) i a *
        (2 / (unitSphereArea (m + 1) *
          ‖outwardUnitNormal (Ω := Ω) x - chartBoundaryTangentialDerivative i a v‖ ^
            (m + 1)))) • outwardUnitNormal (Ω := Ω) x)) := by
  have hminus := tendsto_rescale_normal_sub_chartBoundaryParametrization i a v
    (-outwardUnitNormal (Ω := Ω) x)
  have hplus := tendsto_rescale_normal_sub_chartBoundaryParametrization i a v
    (outwardUnitNormal (Ω := Ω) x)
  rw [hx] at hminus hplus
  simp only [smul_neg, ← sub_eq_add_neg] at hminus
  have hzminus := normal_sub_chartBoundaryTangentialDerivative_ne_zero i ha x hx
    (s := (-1 : ℝ)) (by norm_num) v
  have hzplus := normal_sub_chartBoundaryTangentialDerivative_ne_zero i ha x hx
    (s := (1 : ℝ)) one_ne_zero v
  simp only [neg_one_smul, one_smul] at hzminus hzplus
  have hpair := (tendsto_pow_smul_gradient_fundamentalSolution hm hzminus hminus).sub
    (tendsto_pow_smul_gradient_fundamentalSolution hm hzplus hplus)
  rw [sub_gradient_fundamentalSolution_tangent hm i ha x hx v] at hpair
  have hJ := (tendsto_chartBoundaryJacobian_rescale i a v).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa only [smul_sub, smul_smul] using hJ.smul hpair

end SobolevSpace.Trace.C1
