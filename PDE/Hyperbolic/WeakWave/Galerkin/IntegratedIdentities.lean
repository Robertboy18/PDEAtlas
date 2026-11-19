/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.Solution
public import PDE.Hyperbolic.WeakWave.Galerkin.BochnerRealization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting

/-!
# Integrated identities for weak-wave Galerkin trajectories

We derive the two time-integration identities carrying the initial
displacement and velocity, and the almost-everywhere projected spatial equation
for the canonical Bochner acceleration. The time identities hold against every
ambient energy-space test; only the spatial equation uses the stable trial
projection.

The spatial equation `projectedEquationLpAE` is the identity
`⟨u_m'', v⟩ = (f, v¹) - B[u_m, v¹; t]` in step 3 of the proof of Evans, §7.2.2, Theorem 2, with
the trial projection of `v` in the role of `v¹`. The two time identities each carry one
integration by parts in time with its initial datum; Evans does both at once in step 3 of the
proof of Theorem 3, where he derives from (32) the Galerkin form of (36).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 2, step 3; proof of Theorem 3,
  step 3, equations (32) and (36).
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

omit [CompleteSpace V] [FiniteDimensional ℝ S] [CompleteSpace S] in
/-- Integration by parts in time for the pairing of an absolutely continuous trial-space curve
`x` with a fixed ambient test `v`, written for `L²` representatives `X` of the included curve
and `Y` of the pairing of its derivative `y` with `v`. The test vanishes at `b`. -/
private theorem integral_inner_derivToLp_eq (hab : a ≤ b) {x y : ℝ → S}
    (hxAC : AbsolutelyContinuousOnInterval x a b)
    (hxy : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt x (y t) t) (v : V) (τ : TimeTest a b)
    {X : ℝ → H} (hX : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), X t = T.inclusion (x t : V)) {Y : ℝ → ℝ}
    (hY : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), Y t =
      inner ℝ (T.inclusion (y t : V)) (T.inclusion v)) :
    -(∫ t, inner ℝ (X t) (T.inclusion v) * τ.derivToLp t ∂volume.restrict (Set.Ioc a b)) =
      (∫ t, Y t * τ.toLp t ∂volume.restrict (Set.Ioc a b)) +
        inner ℝ (T.inclusion (x a : V)) (T.inclusion v) * τ.toFun a := by
  let L : S →L[ℝ] ℝ := (innerSL ℝ (T.inclusion v)).comp (T.inclusion.comp S.subtypeL)
  have hL (z : S) : L z = inner ℝ (T.inclusion (z : V)) (T.inclusion v) := real_inner_comm _ _
  have hparts := (L.lipschitzWith.comp_absolutelyContinuousOnInterval
    hxAC).integral_mul_deriv_eq_deriv_mul (τ.absolutelyContinuousOnInterval hab)
  have hleft : (∫ t in a..b, (L ∘ x) t * deriv τ.toFun t) =
      ∫ t, inner ℝ (X t) (T.inclusion v) * τ.derivToLp t ∂volume.restrict (Set.Ioc a b) := by
    rw [intervalIntegral.integral_of_le hab]
    refine integral_congr_ae ?_
    filter_upwards [hX, τ.derivMemLp.coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with
      t hx hτ ht
    rw [hx, show τ.derivToLp t = τ.derivFun t from hτ, Function.comp_apply, hL,
      (τ.hasDerivAt t (Ioc_subset_Icc_self ht)).deriv]
  have hright : (∫ t in a..b, deriv (L ∘ x) t * τ.toFun t) =
      ∫ t, Y t * τ.toLp t ∂volume.restrict (Set.Ioc a b) := by
    rw [intervalIntegral.integral_of_le hab]
    refine integral_congr_ae ?_
    filter_upwards [hxy, hY, τ.memLp.coeFn_toLp] with t ht hy hτ
    rw [hy, show τ.toLp t = τ.toFun t from hτ, (L.hasFDerivAt.comp_hasDerivAt t ht).deriv, hL]
  rw [hleft, hright, τ.final_zero] at hparts
  simp only [Function.comp_apply, hL] at hparts
  linarith

omit [CompleteSpace V] in
/-- The Galerkin displacement and pivot velocity satisfy the full ambient
integrated time-derivative identity, including the prescribed initial
displacement.

Unlike the spatial Galerkin equation, this statement is valid against every
`v : V`: it follows only from the coefficient identity `q' = p` and the
continuous inclusions `S → V → H`. -/
theorem displacementIdentity
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a < b) :
    IsGelfandIntegratedWeakSolution T (fun _ ↦ 0) (fun t ↦ T.pivotToDual (U.velocityLp hab.le t))
      (U.displacementLp hab.le) (T.inclusion (q₀ : V)) := by
  refine ⟨hab, by simp, fun v τ ↦ (integrable_dualTimeTest v τ.toLp
    (T.pivotToDual.compLpL 2 _ (U.velocityLp hab.le))).congr ?_, fun v τ ↦ ?_⟩
  · filter_upwards [T.pivotToDual.coeFn_compLpL (U.velocityLp hab.le)] with t ht
    rw [ht]
  simp only [zero_apply, zero_mul, integral_zero, add_zero]
  simpa only [U.initialDisplacement] using integral_inner_derivToLp_eq hab.le
    U.displacementAbsolutelyContinuous U.displacementEquationAE v τ
    ((U.displacementLp_apply_ae hab.le).mono fun t ht ↦ congrArg T.inclusion ht)
    ((U.velocityLp_apply_ae hab.le).mono fun t ht ↦ congrArg (T.pivotToDual · v) ht)

omit [CompleteSpace V] in
/-- The pivot velocity and the canonical dual acceleration satisfy the
integrated time-derivative identity with the prescribed initial velocity.

This is the second time identity in Evans's weak-wave formulation.  It is
again valid for every ambient test `v : V`; only the separate spatial
equation remains projected at the finite-dimensional level. -/
theorem velocityIdentity {MB : ℝ} {K : NNReal}
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (P : StableTrialProjection T S K) (hab : a ≤ b)
    (ellLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hEll : (ellLp : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)] ell)
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Set.Ioc a b)))
    (hBbound : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖B t‖ ≤ MB) (v : V) (τ : TimeTest a b) :
    -(∫ t, inner ℝ (U.velocityLp hab t) (T.inclusion v) * τ.derivToLp t
          ∂(volume.restrict (Set.Ioc a b))) =
      (∫ t, U.accelerationLp P hab ellLp hBmeas hBbound t v * τ.toLp t
          ∂(volume.restrict (Set.Ioc a b))) +
      inner ℝ (T.inclusion (p₀ : V)) (T.inclusion v) * τ.toFun a := by
  simpa only [U.initialVelocity] using integral_inner_derivToLp_eq hab
    U.velocityAbsolutelyContinuous
    (U.velocityEquationAE.mono fun t ht ↦ by simpa only [coefficientAcceleration] using ht) v τ
    (U.velocityLp_apply_ae hab)
    ((U.accelerationLp_apply_ae P hab ellLp hEll hBmeas hBbound).mono fun t ht ↦ congrArg (· v) ht)

omit [CompleteSpace V] in
/-- Almost-everywhere spatial equation satisfied by a finite-dimensional
Galerkin trajectory.

The acceleration acts on the ambient test `v`, while the stiffness and
forcing act on its trial projection.  This is the precise equation that can
be passed to the limit when the projections converge strongly to the
identity. -/
theorem projectedEquationLpAE {MB : ℝ} {K : NNReal}
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (B t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (P : StableTrialProjection T S K) (hab : a ≤ b)
    (ellLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hEll : (ellLp : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)] ell)
    (hBmeas : AEStronglyMeasurable B (volume.restrict (Set.Ioc a b)))
    (hBbound : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖B t‖ ≤ MB) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ∀ v : V, U.accelerationLp P hab ellLp hBmeas hBbound t v +
      B t (U.displacementLp hab t) (P.energyProjection v : V) =
      ellLp t (P.energyProjection v : V) := by
  filter_upwards [ U.accelerationLp_apply_ae P hab ellLp hEll hBmeas hBbound,
    U.displacementLp_apply_ae hab, hEll] with t hacc hu hellt
  intro v
  rw [hacc, hu, hellt]
  rw [U.dualAcceleration_apply_eq_projected P t v]
  simp only [ambientDisplacement]
  ring

end SecondOrderSolutionOn

end Hyperbolic.Variational
