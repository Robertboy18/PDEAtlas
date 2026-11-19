/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Measurable.Bochner
public import PDE.Analysis.Evolution.Integrated.TimeTestFunction
import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
import PDE.Analysis.Evolution.Integrated.Solution
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Integrated identities for measurable Galerkin trajectories

An absolutely continuous Galerkin approximation satisfies its projected
equation `⟪u'(t), v⟫_H + B(t)(u(t), v) = ℓ(t)(v)` only for almost every `t`.
To pass to weak limits one needs the equation in integrated form: multiplying
by a time test `τ`, integrating over `[a, b]`, and moving the time derivative
onto `τ` by integration by parts (valid because `t ↦ ⟪u(t), v⟫_H` is
absolutely continuous) gives

`-∫_a^b ⟪u, v⟫_H τ' + ∫_a^b B(t)(u, v) τ = ∫_a^b ℓ(t)(v) τ + ⟪u₀, v⟫_H τ(a)`,

in which only the initial value `u(a) = u₀` appears as a boundary term. We
prove the identity first for the stored representatives, with the two
integrability hypotheses left explicit, and then for the Bochner `L²` classes,
where strong measurability and an essential bound on `B` supply the
integrability of the form term and the `L²` class of the derivative supplies
the rest.  This is the form in which the Galerkin equations are passed to the
limit in Evans's existence proof.

## Main results

* `AEGelfandGalerkinApproximation.integratedInitialIdentity_interval`: the
  identity for the pointwise representatives.
* `AEGelfandGalerkinApproximation.integratedInitialIdentity`: the identity
  for the Bochner classes `ambientTrajectoryLp`, `τ.toLp` and
  `τ.derivToLp`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, proof of Theorem 3, equations (32)-(34) (the
  equations integrated against test functions vanishing at the final time).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis.Evolution

namespace AEGelfandGalerkinApproximation

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {T : GelfandTriple (V := V) (H := H)}
  {S : Submodule ℝ V}
  {B : ℝ → V →L[ℝ] StrongDual ℝ V}
  {ell : ℝ → StrongDual ℝ V}
  {a b C M : ℝ} {u₀ : S}

omit [CompleteSpace V] [CompleteSpace H] in
/-- The integrated initial-value identity for an almost-everywhere Galerkin equation, for
the pointwise representatives, assuming interval integrability of the derivative term and
of the form term. -/
theorem integratedInitialIdentity_interval
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) (v : S) (τ : TimeTest a b)
    (hderivative : IntervalIntegrable
      (fun t ↦ inner ℝ
        (T.inclusion (G.coefficientDerivative t : V))
        (T.inclusion (v : V)) * τ.toFun t) volume a b)
    (hform : IntervalIntegrable
      (fun t ↦ B t (G.trajectory t : V) (v : V) * τ.toFun t)
        volume a b) :
    -(∫ t in a..b,
        inner ℝ (T.inclusion (G.trajectory t : V))
          (T.inclusion (v : V)) * τ.derivFun t) +
        ∫ t in a..b,
          B t (G.trajectory t : V) (v : V) * τ.toFun t =
      (∫ t in a..b, ell t (v : V) * τ.toFun t) +
        inner ℝ (T.inclusion (u₀ : V)) (T.inclusion (v : V)) *
          τ.toFun a := by
  have heqint :
      (∫ t in a..b,
        inner ℝ (T.inclusion (G.coefficientDerivative t : V))
          (T.inclusion (v : V)) * τ.toFun t) +
          ∫ t in a..b,
            B t (G.trajectory t : V) (v : V) * τ.toFun t =
        ∫ t in a..b, ell t (v : V) * τ.toFun t := by
    rw [← intervalIntegral.integral_add hderivative hform]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 G.equation_ae] with t ht hmem
    rw [← add_mul, ht (by simpa only [Set.uIoc_of_le hab] using hmem) v]
  have htrajectoryAC :
      AbsolutelyContinuousOnInterval (fun t ↦ T.inclusion (G.trajectory t : V)) a b := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using
      (T.inclusion.comp S.subtypeL).lipschitzWith.comp_absolutelyContinuousOnInterval
        G.trajectory_ac
  have hderivativeAE :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        HasDerivAt (fun s ↦ T.inclusion (G.trajectory s : V))
          (T.inclusion (G.coefficientDerivative t : V)) t :=
    G.derivative_ae.mono fun t ht ↦ (T.inclusion.comp S.subtypeL).hasFDerivAt.comp_hasDerivAt t ht
  have hparts := τ.integrationByParts_inner hab (T.inclusion (v : V)) htrajectoryAC hderivativeAE
  rw [G.initial] at hparts
  linarith

omit [CompleteSpace V] [CompleteSpace H] in
/-- Bochner `L²` form of the measurable-time Galerkin identity.

Strong measurability and an essential operator-norm bound on `B` provide the
integrability of the form term. The derivative term follows from the
`L²` class of the coefficient derivative. -/
theorem integratedInitialIdentity
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (v : S) (τ : TimeTest a b) :
    -(∫ t,
        inner ℝ (T.inclusion (G.ambientTrajectoryLp hab t))
          (T.inclusion (v : V)) * τ.derivToLp t
          ∂(volume.restrict (Set.Ioc a b))) +
        ∫ t, B t (G.ambientTrajectoryLp hab t) (v : V) * τ.toLp t
          ∂(volume.restrict (Set.Ioc a b)) =
      (∫ t, ell t (v : V) * τ.toLp t
        ∂(volume.restrict (Set.Ioc a b))) +
        inner ℝ (T.inclusion (u₀ : V)) (T.inclusion (v : V)) *
          τ.toFun a := by
  let μab := volume.restrict (Set.Ioc a b)
  have hτ : (τ.toLp : ℝ → ℝ) =ᵐ[μab] τ.toFun := τ.memLp.coeFn_toLp
  have hdτ : (τ.derivToLp : ℝ → ℝ) =ᵐ[μab] τ.derivFun := τ.derivMemLp.coeFn_toLp
  have hderivative : IntervalIntegrable
      (fun t ↦ inner ℝ (T.inclusion (G.coefficientDerivative t : V))
        (T.inclusion (v : V)) * τ.toFun t) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 <|
      (integrable_gelfandPivotTimeTest T (v : V) τ.toLp G.ambientDerivativeLp).congr <| by
        filter_upwards [G.ambientDerivativeLp_apply_ae, hτ] with t hGt hτt
        rw [hGt, hτt]
  have hform : IntervalIntegrable
      (fun t ↦ B t (G.trajectory t : V) (v : V) * τ.toFun t) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 <|
      (integrable_timeDependentBilinearTimeTest B (v : V) τ.toLp hBmeas MB hBbound
        (G.ambientTrajectoryLp hab)).congr <| by
        filter_upwards [G.ambientTrajectoryLp_apply_ae hab, hτ] with t hGt hτt
        rw [hGt, hτt]
  convert G.integratedInitialIdentity_interval hab v τ hderivative hform using 3 <;>
    rw [intervalIntegral.integral_of_le hab] <;> refine integral_congr_ae ?_ <;>
    filter_upwards [G.ambientTrajectoryLp_apply_ae hab, hτ, hdτ] with t hGt hτt hdτt
  · rw [hGt, hdτt]
  · rw [hGt, hτt]
  · rw [hτt]

end AEGelfandGalerkinApproximation

end PDE.Analysis.Evolution
