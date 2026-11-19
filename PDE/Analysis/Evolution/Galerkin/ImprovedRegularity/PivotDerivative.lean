/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Measurable.Bochner
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Pivot derivatives of Galerkin trajectories

For a Galerkin trajectory in an energy space `V`, Evans's first improved
regularity estimate controls the coefficient derivative after inclusion into
the pivot Hilbert space `H`. We realize that derivative as a Bochner `L²(H)`
class and prove, by integration by parts, that its image under `pivotToDual` is the
Gelfand weak time derivative of the ambient trajectory.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, proof of Theorem 5, step 2 (the bound for
  `u_m'` in `L²(0, T; L²(U))`). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

/-! ## Pivot-valued Galerkin derivatives -/

section PivotDerivative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
The Bochner class in `L²(a, b; H)` of the included coefficient derivative `J uₘ'`. Evans's
first regularity improvement bounds the Galerkin derivatives in this space.
-/
def AEGelfandGalerkinApproximation.pivotDerivativeLp
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V)
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀) :
    Lp H 2 (volume.restrict (Set.Ioc a b)) :=
  (T.inclusion.comp S.subtypeL).compLpL 2
    (volume.restrict (Set.Ioc a b)) G.coefficientDerivativeLp

/--
The pivot-space Bochner derivative agrees almost everywhere with the
pointwise inclusion of the chosen coefficient derivative.
-/
theorem AEGelfandGalerkinApproximation.pivotDerivativeLp_apply_ae
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V)
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀) :
    (G.pivotDerivativeLp T S : ℝ → H) =ᵐ[
      volume.restrict (Set.Ioc a b)]
        fun t ↦ T.inclusion (G.coefficientDerivative t : V) := by
  filter_upwards [
    (T.inclusion.comp S.subtypeL).coeFn_compLpL G.coefficientDerivativeLp,
    G.coefficientDerivativeLp_apply_ae] with t hcomp hderiv
  unfold pivotDerivativeLp
  rw [hcomp, hderiv]
  rfl

/--
The image of `J uₘ'` under `pivotToDual` is the Gelfand weak time derivative of the
ambient Galerkin trajectory, tested against every `v ∈ V`. The proof is integration by parts
in time.
-/
theorem AEGelfandGalerkinApproximation.hasGelfandWeakTimeDerivativeOn_pivotDerivativeLp
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V)
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) :
    HasGelfandWeakTimeDerivativeOn T
      (G.ambientTrajectoryLp hab)
      (T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b))
        (G.pivotDerivativeLp T S)) := by
  intro v τ hτa
  let μab := volume.restrict (Set.Ioc a b)
  let J : S →L[ℝ] H := T.inclusion.comp S.subtypeL
  have hτ : (τ.toLp : ℝ → ℝ) =ᵐ[μab] τ.toFun := τ.memLp.coeFn_toLp
  have hdτ : (τ.derivToLp : ℝ → ℝ) =ᵐ[μab] τ.derivFun := τ.derivMemLp.coeFn_toLp
  have htrajectoryAC : AbsolutelyContinuousOnInterval (fun t ↦ J (G.trajectory t)) a b :=
    J.lipschitzWith.comp_absolutelyContinuousOnInterval G.trajectory_ac
  have hparts := τ.integrationByParts_inner hab (T.inclusion v) htrajectoryAC
    (G.derivative_ae.mono fun t ht ↦ J.hasFDerivAt.comp_hasDerivAt t ht)
  rw [hτa, mul_zero, add_zero] at hparts
  have hgInt :
      (∫ t, (T.pivotToDual.compLpL 2 μab (G.pivotDerivativeLp T S)) t v * τ.toLp t ∂μab) =
        ∫ t in a..b, inner ℝ (J (G.coefficientDerivative t)) (T.inclusion v) * τ.toFun t := by
    rw [intervalIntegral.integral_of_le hab]
    refine integral_congr_ae ?_
    filter_upwards [T.pivotToDual.coeFn_compLpL (G.pivotDerivativeLp T S),
      G.pivotDerivativeLp_apply_ae T S, hτ] with t hdual hdu hτt
    rw [hdual, hdu, hτt]
    rfl
  have huInt :
      (∫ t, inner ℝ (T.inclusion (G.ambientTrajectoryLp hab t)) (T.inclusion v) *
          τ.derivToLp t ∂μab) =
        ∫ t in a..b, inner ℝ (J (G.trajectory t)) (T.inclusion v) * τ.derivFun t := by
    rw [intervalIntegral.integral_of_le hab]
    refine integral_congr_ae ?_
    filter_upwards [G.ambientTrajectoryLp_apply_ae hab, hdτ] with t hu hdτt
    rw [hu, hdτt]
    rfl
  rw [hgInt, huInt]
  linarith

end PivotDerivative

end PDE.Analysis.Evolution
