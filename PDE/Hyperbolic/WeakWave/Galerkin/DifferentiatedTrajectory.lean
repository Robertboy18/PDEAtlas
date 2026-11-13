/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Hyperbolic.Variational.SecondOrder.AutonomousDifferentiation
public import PDE.Hyperbolic.WeakWave.Galerkin.BochnerRealization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Differentiated weak-wave Galerkin trajectories

For an autonomous form `B(t) = A` and forcing `ℓ` that is absolutely continuous with
derivative `ℓ̇`, differentiating the Galerkin ODE in time produces a second
`SecondOrderSolutionOn` trajectory `D = U.timeDerivative` whose displacement is
`U'` and whose velocity is `U''`.  This is the standard device for improved
regularity of weak solutions to hyperbolic equations: estimates proved for an
arbitrary trajectory apply to `D`, and so control one more time derivative of `U`.

We prove the identifications between the Bochner realizations
of `D` and those of `U` from `BochnerRealization`.  Everything is pointwise and
follows from the defining equations of `timeDerivative`; no uniqueness of weak
derivatives is invoked.

## Main results

* `inclusion_compLpL_timeDerivative_displacementLp`: in `L²(a,b;H)`, the
  displacement of `D` (included into the pivot space) is the velocity of `U`.
* `pivotToDual_compLpL_timeDerivative_velocityLp`: in `L²(a,b;V*)`, the velocity of
  `D` (mapped to the dual) is the canonical acceleration `U.accelerationLp`.
* `hasIdentityGelfandWeakTimeDerivativeOn_timeDerivative_displacementLp`: the
  displacement of `U` has the displacement of `D` as its `V`-valued weak time
  derivative, stated on the identity Gelfand triple of `V` so that the energy-space
  identity, not only the pivot-space one, is available.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, proof of Theorem 5, step 2, equations (53)-(55).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

namespace SecondOrderSolutionOn

variable
  {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {T : GelfandTriple (V := V) (H := H)}
  {S : Submodule ℝ V} [FiniteDimensional ℝ S] [CompleteSpace S]
  {B : ℝ → V →L[ℝ] StrongDual ℝ V}
  {ell : ℝ → StrongDual ℝ V}
  {a b : ℝ} {q₀ p₀ : S}

/-! ## Exact links to the differentiated autonomous trajectory -/

omit [CompleteSpace V] in
/--
The displacement of the differentiated autonomous Galerkin trajectory is
exactly the original velocity after both are realized in Bochner space.

This is the finite-dimensional identity `J (dU) = U_t` used in the paired
compactness argument. It follows from the pointwise definition of
`SecondOrderSolutionOn.timeDerivative`.
-/
theorem inclusion_compLpL_timeDerivative_displacementLp {A : V →L[ℝ] StrongDual ℝ V}
    {ellDot : ℝ → StrongDual ℝ V}
    (U : SecondOrderSolutionOn (fun _ ↦ gelfandGalerkinOperator T S A)
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) (hforcingAC : AbsolutelyContinuousOnInterval (gelfandGalerkinForcing T S ell) a b)
    (hforcingDeriv : ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      HasDerivAt (gelfandGalerkinForcing T S ell) (gelfandGalerkinForcing T S ellDot t) t) :
    T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b))
        ((U.timeDerivative hforcingAC hforcingDeriv).displacementLp hab) = U.velocityLp hab := by
  let D := U.timeDerivative hforcingAC hforcingDeriv
  refine Lp.ext ?_
  filter_upwards [T.inclusion.coeFn_compLpL (D.displacementLp hab), D.displacementLp_apply_ae hab,
    U.velocityLp_apply_ae hab] with t hinclusion hD hU
  rw [hinclusion, hD, hU]
  rfl

omit [CompleteSpace V] in
/--
The pivot velocity of the differentiated autonomous Galerkin trajectory is
exactly the original canonical dual acceleration.

The stable projection and forcing hypotheses are precisely those already
needed to realize the original residual as `U.accelerationLp`.  Pointwise,
the statement is the defining equality
`D.velocity = -K U.displacement + forcing`.
-/
theorem pivotToDual_compLpL_timeDerivative_velocityLp {A : V →L[ℝ] StrongDual ℝ V}
    {ellDot : ℝ → StrongDual ℝ V} {MB : ℝ} {K : NNReal}
    (U : SecondOrderSolutionOn (fun _ ↦ gelfandGalerkinOperator T S A)
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (P : StableTrialProjection T S K) (hab : a ≤ b)
    (ellLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hEll : (ellLp : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)] ell)
    (hAmeas : AEStronglyMeasurable (fun _ : ℝ ↦ A) (volume.restrict (Set.Ioc a b)))
    (hAbound : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖(fun _ : ℝ ↦ A) t‖ ≤ MB)
    (hforcingAC : AbsolutelyContinuousOnInterval (gelfandGalerkinForcing T S ell) a b)
    (hforcingDeriv : ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      HasDerivAt (gelfandGalerkinForcing T S ell) (gelfandGalerkinForcing T S ellDot t) t) :
    T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) ((U.timeDerivative hforcingAC
      hforcingDeriv).velocityLp hab) = U.accelerationLp P hab ellLp hAmeas hAbound := by
  let D := U.timeDerivative hforcingAC hforcingDeriv
  refine Lp.ext ?_
  filter_upwards [T.pivotToDual.coeFn_compLpL (D.velocityLp hab), D.velocityLp_apply_ae hab,
    U.accelerationLp_apply_ae P hab ellLp hEll hAmeas hAbound] with t hpivot hD hU
  rw [hpivot, hD, hU]
  rfl

omit [CompleteSpace V] in
/--
The original Galerkin displacement has the differentiated trajectory's
displacement as its `V`-valued weak derivative.

Using the identity Gelfand triple records the stronger energy-space identity
needed by improved regularity, rather than only the original pivot-space
identity.  The proof uses the stored pointwise equation
`U.displacement' = U.velocity` and the defining equality
`D.displacement = U.velocity`.
-/
theorem hasIdentityGelfandWeakTimeDerivativeOn_timeDerivative_displacementLp
    {A : V →L[ℝ] StrongDual ℝ V} {ellDot : ℝ → StrongDual ℝ V}
    (U : SecondOrderSolutionOn (fun _ ↦ gelfandGalerkinOperator T S A)
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) (hforcingAC : AbsolutelyContinuousOnInterval (gelfandGalerkinForcing T S ell) a b)
    (hforcingDeriv : ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      HasDerivAt (gelfandGalerkinForcing T S ell) (gelfandGalerkinForcing T S ellDot t) t) :
    HasGelfandWeakTimeDerivativeOn (GelfandTriple.identity V) (U.displacementLp hab)
      ((GelfandTriple.identity V).energyToDual.compLpL 2 (volume.restrict (Set.Ioc a b))
        ((U.timeDerivative hforcingAC hforcingDeriv).displacementLp hab)) := by
  let D := U.timeDerivative hforcingAC hforcingDeriv
  intro v τ hτa
  let L : S →L[ℝ] ℝ := (innerSL ℝ v).comp S.subtypeL
  have hL (z : S) : L z = inner ℝ (z : V) v := real_inner_comm _ _
  have hparts := (L.lipschitzWith.comp_absolutelyContinuousOnInterval
    U.displacementAbsolutelyContinuous).integral_mul_deriv_eq_deriv_mul
      (τ.absolutelyContinuousOnInterval hab)
  have hleft : (∫ t in a..b, (L ∘ U.displacement) t * deriv τ.toFun t) =
      ∫ t, inner ℝ (U.displacementLp hab t) v * τ.derivToLp t ∂volume.restrict (Set.Ioc a b) := by
    rw [intervalIntegral.integral_of_le hab]
    refine integral_congr_ae ?_
    filter_upwards [U.displacementLp_apply_ae hab, τ.derivMemLp.coeFn_toLp,
      ae_restrict_mem measurableSet_Ioc] with t hu hτ ht
    rw [hu, show τ.derivToLp t = τ.derivFun t from hτ, Function.comp_apply, hL,
      (τ.hasDerivAt t (Ioc_subset_Icc_self ht)).deriv]
    rfl
  have hright : (∫ t in a..b, deriv (L ∘ U.displacement) t * τ.toFun t) =
      ∫ t, ((GelfandTriple.identity V).energyToDual.compLpL 2 (volume.restrict (Set.Ioc a b))
        (D.displacementLp hab)) t v * τ.toLp t ∂volume.restrict (Set.Ioc a b) := by
    rw [intervalIntegral.integral_of_le hab]
    refine integral_congr_ae ?_
    filter_upwards [U.displacementEquationAE,
      (GelfandTriple.identity V).energyToDual.coeFn_compLpL (D.displacementLp hab),
      D.displacementLp_apply_ae hab, τ.memLp.coeFn_toLp] with t ht hdual hD hτ
    rw [hdual, hD, show τ.toLp t = τ.toFun t from hτ, (L.hasFDerivAt.comp_hasDerivAt t ht).deriv,
      hL]
    rfl
  rw [hleft, hright, τ.final_zero, hτa] at hparts
  simp only [GelfandTriple.identity_inclusion_apply]
  linarith

end SecondOrderSolutionOn

end Hyperbolic.Variational
