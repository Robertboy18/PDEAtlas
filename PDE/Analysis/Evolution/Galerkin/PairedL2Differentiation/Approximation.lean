/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Gelfand.VectorField
public import PDE.Analysis.Evolution.Galerkin.ImprovedRegularity.PivotDerivative
import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
import PDE.Analysis.Evolution.Galerkin.AutonomousDifferentiation
import PDE.Analysis.Evolution.Galerkin.Gelfand.Existence
import PDE.Analysis.Evolution.ODE.AutonomousDifferentiation
import PDE.Analysis.Evolution.Galerkin.Measurable.Energy
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Differentiated Galerkin approximations with an `L²` load

Improved regularity for the autonomous Galerkin equation
`⟪u', v⟫_H + B(u, v) = ℓ(t)(v)` is obtained by differentiating in time: the
velocity `w = u'` solves the same equation with load `ℓ'`, and the energy
estimate for `w` bounds `u'` in `L²(a, b; V)`.  When `ℓ` is absolutely
continuous with derivative `ℓ' ∈ L²(a, b; V*)` only, the differentiated
equation has no pointwise forcing bound, so the pointwise-in-time energy field
of `AEGelfandGalerkinApproximation` is unavailable.  We introduce the
structure `L2DifferentiatedGalerkinApproximation` (an absolutely continuous
trajectory with an almost-everywhere `L²` derivative satisfying the projected
equation), construct it as the velocity of an autonomous approximation, prove
the coercive estimate
`(C/2) ‖w‖²_{L²(V)} ≤ ½ ‖w(a)‖²_H + ‖ℓ'‖²_{L²(V*)} / (2C)` directly from the
absolutely continuous energy identity, and prove the integrated projected
equation. The differentiated load needs no pointwise bound.

## Main results

* `L2DifferentiatedGalerkinApproximation`: the structure.
* `L2DifferentiatedGalerkinApproximation.exists_of_autonomous`: the velocity
  of an autonomous approximation is a differentiated approximation with load
  `ℓ'` and initial value the Galerkin vector field at `a`.
* `L2DifferentiatedGalerkinApproximation.norm_ambientTrajectoryLp_sq_le`:
  the coercive `L²(V)` bound in terms of `‖ℓ'‖_{L²(V*)}`.
* `L2DifferentiatedGalerkinApproximation.integratedInitialIdentity`: the
  integrated projected equation for the Bochner classes.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, proof of Theorem 5, step 4, equations (50) and
  (51) (the Galerkin equations differentiated in time). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
A differentiated finite-dimensional Galerkin trajectory driven by an
`L²(V*)` load.

It is an absolutely continuous trajectory with an `L²` derivative satisfying the projected
equation almost everywhere. Unlike `AEGelfandGalerkinApproximation`, it carries no pointwise
forcing constant and no stored energy estimate.
-/
structure L2DifferentiatedGalerkinApproximation
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V)
    (B : V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    (a b : ℝ) (u₀ : S) where
  /-- The differentiated Galerkin state. -/
  trajectory : ℝ → S
  /-- Its almost-everywhere finite-dimensional derivative. -/
  coefficientDerivative : ℝ → S
  /-- Initial value of the differentiated state. -/
  initial : trajectory a = u₀
  /-- Absolute continuity on the closed evolution interval. -/
  absolutelyContinuousOnInterval : AbsolutelyContinuousOnInterval trajectory a b
  /-- Identification of the chosen derivative almost everywhere. -/
  derivativeAE :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      HasDerivAt trajectory (coefficientDerivative t) t
  /-- Square-integrability of the finite-dimensional derivative. -/
  derivativeMemLp :
    MemLp coefficientDerivative 2 (volume.restrict (Set.Ioc a b))
  /-- The differentiated projected equation. -/
  equationAE :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ∀ v : S,
      inner ℝ (T.inclusion (coefficientDerivative t : V))
          (T.inclusion (v : V)) +
        B (trajectory t : V) (v : V) =
      ell t (v : V)

namespace L2DifferentiatedGalerkinApproximation

variable
    {T : GelfandTriple (V := V) (H := H)}
    {S : Submodule ℝ V}
    {B : V →L[ℝ] StrongDual ℝ V}
    {ell : ℝ → StrongDual ℝ V}
    {a b : ℝ} {u₀ : S}

omit [CompleteSpace V] [CompleteSpace H] in
/-- The differentiated trajectory defines a Bochner `L²(V)` class. -/
theorem trajectoryMemLp
    (G : L2DifferentiatedGalerkinApproximation T S B ell a b u₀)
    (hab : a ≤ b) :
    MemLp G.trajectory 2 (volume.restrict (Set.Ioc a b)) := by
  apply memLp_restrict_Ioc_of_continuousOn
  simpa only [Set.uIcc_of_le hab] using G.absolutelyContinuousOnInterval.continuousOn

/-- The ambient energy-space class of a differentiated trajectory. -/
def ambientTrajectoryLp
    (G : L2DifferentiatedGalerkinApproximation T S B ell a b u₀)
    (hab : a ≤ b) :
    Lp V 2 (volume.restrict (Set.Ioc a b)) :=
  S.subtypeL.compLpL 2 (volume.restrict (Set.Ioc a b))
    ((G.trajectoryMemLp hab).toLp G.trajectory)

omit [CompleteSpace V] [CompleteSpace H] in
/-- Pointwise representative of `ambientTrajectoryLp`. -/
theorem ambientTrajectoryLp_apply_ae
    (G : L2DifferentiatedGalerkinApproximation T S B ell a b u₀)
    (hab : a ≤ b) :
    (G.ambientTrajectoryLp hab : ℝ → V) =ᵐ[
      volume.restrict (Set.Ioc a b)] fun t ↦ (G.trajectory t : V) := by
  filter_upwards
      [S.subtypeL.coeFn_compLpL
          ((G.trajectoryMemLp hab).toLp G.trajectory),
        (G.trajectoryMemLp hab).coeFn_toLp] with t hcomp htrajectory
  change
    ((S.subtypeL.compLpL 2 (volume.restrict (Set.Ioc a b))
      ((G.trajectoryMemLp hab).toLp G.trajectory) :
        Lp V 2 (volume.restrict (Set.Ioc a b))) t) =
      (G.trajectory t : V)
  rw [hcomp, htrajectory]
  rfl

omit [CompleteSpace V] [CompleteSpace H] in
/--
Differentiate one autonomous Galerkin trajectory with an `L²` derivative
of the load.

If `ℓ` is absolutely continuous with `ℓ' = ellDot ∈ L²(a, b; V*)`, the velocity of the
autonomous approximation `G` is a differentiated approximation with load `ellDot`, whose
initial value is the Galerkin vector field at `a`.
-/
theorem exists_of_autonomous
    [FiniteDimensional ℝ S] [CompleteSpace S]
    {C M : ℝ} {ellDot : ℝ → StrongDual ℝ V}
    (G : AEGelfandGalerkinApproximation T S (fun _ ↦ B) ell
      a b C M u₀)
    (hab : a ≤ b)
    (hellAC : AbsolutelyContinuousOnInterval ell a b)
    (hellDeriv :
      ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt ell (ellDot t) t)
    (hellDot : MemLp ellDot 2 (volume.restrict (Set.Ioc a b))) :
    ∃ DG : L2DifferentiatedGalerkinApproximation
        T S B ellDot a b
          (gelfandGalerkinVectorField T S (fun _ ↦ B) ell a u₀),
      DG.trajectory =ᵐ[volume.restrict (Set.Ioc a b)]
          G.coefficientDerivative ∧
      T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b))
          (DG.ambientTrajectoryLp hab) =
        G.pivotDerivativeLp T S := by
  let A : S →L[ℝ] S := -(gelfandGalerkinOperator T S B)
  let fS : ℝ → S := fun t ↦ (gelfandGalerkinForcingMap T S) (ell t)
  let fDotS : ℝ → S := fun t ↦ (gelfandGalerkinForcingMap T S) (ellDot t)
  let U : AffineCaratheodorySolutionOn (fun _ ↦ A) fS a b u₀ := G.toAutonomousCaratheodory
  let DU : AffineCaratheodorySolutionOn (fun _ ↦ A) fDotS a b (A u₀ + fS a) :=
    U.autonomousVelocitySolution
      (AEGelfandGalerkinApproximation.absolutelyContinuousOnInterval_gelfandGalerkinForcing
        (T := T) (S := S) hellAC)
      (AEGelfandGalerkinApproximation.hasDerivAt_gelfandGalerkinForcing_ae
        (T := T) (S := S) hellDeriv)
  have hfield := neg_gelfandGalerkinOperator_add_forcing T S (fun _ ↦ B)
  have hDUMem : MemLp DU.trajectory 2 (volume.restrict (Set.Ioc a b)) :=
    memLp_restrict_Ioc_of_continuousOn
      (by simpa only [Set.uIcc_of_le hab] using DU.absolutely_continuous.continuousOn)
  let DG : L2DifferentiatedGalerkinApproximation T S B ellDot a b
      (gelfandGalerkinVectorField T S (fun _ ↦ B) ell a u₀) :=
    { trajectory := DU.trajectory
      coefficientDerivative := fun t ↦
        gelfandGalerkinVectorField T S (fun _ ↦ B) ellDot t (DU.trajectory t)
      initial := DU.initial_value.trans (hfield ell a u₀)
      absolutelyContinuousOnInterval := DU.absolutely_continuous
      derivativeAE := DU.equation_ae.mono fun t ht ↦ ht.congr_deriv (hfield ellDot t _)
      derivativeMemLp := (memLp_congr_ae (.of_forall fun t ↦ hfield ellDot t (DU.trajectory t))).1
        ((hDUMem.continuousLinearMap_comp A).add
          (hellDot.continuousLinearMap_comp (gelfandGalerkinForcingMap T S)))
      equationAE := .of_forall fun t ↦
        gelfandGalerkinVectorField_equation T S (fun _ ↦ B) ellDot t (DU.trajectory t) }
  have htrajectory :
      DG.trajectory =ᵐ[volume.restrict (Set.Ioc a b)] G.coefficientDerivative := by
    filter_upwards [G.equation_ae] with t ht
    change U.autonomousVelocity t = G.coefficientDerivative t
    rw [gelfandGalerkin_derivative_eq_vectorField T S (fun _ ↦ B) ell t (G.trajectory t)
      (G.coefficientDerivative t) ht]
    exact hfield ell t (G.trajectory t)
  refine ⟨DG, htrajectory, Lp.ext ?_⟩
  filter_upwards [T.inclusion.coeFn_compLpL (DG.ambientTrajectoryLp hab),
    DG.ambientTrajectoryLp_apply_ae hab, G.pivotDerivativeLp_apply_ae T S, htrajectory]
    with t hleft hDG hright htrajectoryAt
  rw [hleft, hDG, hright, htrajectoryAt]

omit [CompleteSpace V] [CompleteSpace H] in
/--
Natural coercive bound for the differentiated trajectory with an `L²`
load.

`‖w‖²_{L²(V)} ≤ (2/C) (½ ‖ι w(a)‖²_H + ‖ℓ‖²_{L²(V*)} / (2C))`.
-/
theorem norm_ambientTrajectoryLp_sq_le
    {C : ℝ}
    (G : L2DifferentiatedGalerkinApproximation T S B ell a b u₀)
    (hab : a ≤ b) (hC : 0 < C)
    (hcoercive : ∀ w : V, C * ‖w‖ ^ 2 ≤ B w w)
    (hell : MemLp ell 2 (volume.restrict (Set.Ioc a b))) :
    ‖G.ambientTrajectoryLp hab‖ ^ 2 ≤
      (2 / C) * ((1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
        (1 / (2 * C)) * ‖hell.toLp ell‖ ^ 2) := by
  have henergy := gelfandGalerkin_integrated_energy_bound_of_forcing_memLp T S
    (fun _ ↦ B) ell G.trajectory G.coefficientDerivative hab hC
    G.absolutelyContinuousOnInterval G.derivativeAE G.derivativeMemLp (fun _ _ ↦ hcoercive) hell
    G.equationAE
  rw [G.initial] at henergy
  rw [Lp.norm_sq_eq_integral_norm_sq, Lp.norm_sq_eq_integral_norm_sq,
    integral_congr_ae ((G.ambientTrajectoryLp_apply_ae hab).mono fun _ h ↦ congrArg (‖·‖ ^ 2) h),
    integral_congr_ae (hell.coeFn_toLp.mono fun _ h ↦ congrArg (‖·‖ ^ 2) h),
    div_mul_eq_mul_div, le_div_iff₀ hC]
  linarith [sq_nonneg ‖T.inclusion (G.trajectory b : V)‖]

omit [CompleteSpace V] [CompleteSpace H] in
/-- Multiplying the projected equation by a time test gives an integral balance.
Hölder's inequality supplies the velocity term directly from the `L²` derivative. -/
private theorem integral_projected_equation
    (G : L2DifferentiatedGalerkinApproximation T S B ell a b u₀)
    (hab : a ≤ b) (v : S) (τ : TimeTest a b)
    (hform : IntervalIntegrable
      (fun t ↦ B (G.trajectory t : V) (v : V) * τ.toFun t) volume a b) :
    (∫ t in a..b, inner ℝ (T.inclusion (G.coefficientDerivative t : V))
        (T.inclusion (v : V)) * τ.toFun t) +
        ∫ t in a..b, B (G.trajectory t : V) (v : V) * τ.toFun t =
      ∫ t in a..b, ell t (v : V) * τ.toFun t := by
  have hderivative : IntervalIntegrable
      (fun t ↦ inner ℝ (T.inclusion (G.coefficientDerivative t : V))
        (T.inclusion (v : V)) * τ.toFun t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have hdu := G.derivativeMemLp.continuousLinearMap_comp (T.inclusion.comp S.subtypeL)
    exact (hdu.inner_const (T.inclusion (v : V))).integrable_mul τ.memLp
  rw [← intervalIntegral.integral_add hderivative hform,
    intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  apply integral_congr_ae
  filter_upwards [G.equationAE] with t ht
  rw [← add_mul, ht v]

omit [CompleteSpace V] [CompleteSpace H] in
/-- The integrated projected equation for the Bochner classes,
`-∫ ⟪ι w, ι v⟫_H τ' + ∫ B(w, v) τ = ∫ ℓ(t)(v) τ + ⟪ι w(a), ι v⟫_H τ(a)`. -/
theorem integratedInitialIdentity
    (G : L2DifferentiatedGalerkinApproximation T S B ell a b u₀)
    (hab : a ≤ b)
    (hBmeas : AEStronglyMeasurable (fun _ : ℝ ↦ B)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ _t ∂(volume.restrict (Set.Ioc a b)), ‖B‖ ≤ MB)
    (v : S) (τ : TimeTest a b) :
    -(∫ t,
        inner ℝ (T.inclusion (G.ambientTrajectoryLp hab t))
          (T.inclusion (v : V)) * τ.derivToLp t
          ∂(volume.restrict (Set.Ioc a b))) +
        ∫ t, B (G.ambientTrajectoryLp hab t) (v : V) * τ.toLp t
          ∂(volume.restrict (Set.Ioc a b)) =
      (∫ t, ell t (v : V) * τ.toLp t
        ∂(volume.restrict (Set.Ioc a b))) +
        inner ℝ (T.inclusion (u₀ : V)) (T.inclusion (v : V)) *
          τ.toFun a := by
  let μab := volume.restrict (Set.Ioc a b)
  have hτ : (τ.toLp : ℝ → ℝ) =ᵐ[μab] τ.toFun := τ.memLp.coeFn_toLp
  have hdτ : (τ.derivToLp : ℝ → ℝ) =ᵐ[μab] τ.derivFun := τ.derivMemLp.coeFn_toLp
  have hG := G.ambientTrajectoryLp_apply_ae hab
  have hformInterval :
      IntervalIntegrable (fun t ↦ B (G.trajectory t : V) (v : V) * τ.toFun t) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 <|
      (integrable_timeDependentBilinearTimeTest (fun _ : ℝ ↦ B) (v : V) τ.toLp
        (fun v ↦ hBmeas.apply_continuousLinearMap v) MB hBbound (G.ambientTrajectoryLp hab)).congr
        (by filter_upwards [hG, hτ] with t hGt hτt; rw [hGt, hτt])
  have heqint := G.integral_projected_equation hab v τ hformInterval
  have hderivativeAE : ∀ᵐ t ∂μab, HasDerivAt (fun s ↦ T.inclusion (G.trajectory s : V))
      (T.inclusion (G.coefficientDerivative t : V)) t :=
    G.derivativeAE.mono fun t ht ↦ (T.inclusion.comp S.subtypeL).hasFDerivAt.comp_hasDerivAt t ht
  have hparts := τ.integrationByParts_inner hab (T.inclusion (v : V))
    (by simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply] using (T.inclusion.comp S.subtypeL).lipschitzWith
        |>.comp_absolutelyContinuousOnInterval G.absolutelyContinuousOnInterval) hderivativeAE
  rw [G.initial] at hparts
  have htime :
      (∫ t, inner ℝ (T.inclusion (G.ambientTrajectoryLp hab t))
          (T.inclusion (v : V)) * τ.derivToLp t ∂μab) =
        ∫ t in a..b, inner ℝ (T.inclusion (G.trajectory t : V)) (T.inclusion (v : V)) *
          τ.derivFun t := by
    rw [intervalIntegral.integral_of_le hab]
    exact integral_congr_ae (by filter_upwards [hG, hdτ] with t hGt hdt; rw [hGt, hdt])
  have hform : (∫ t, B (G.ambientTrajectoryLp hab t) (v : V) * τ.toLp t ∂μab) =
      ∫ t in a..b, B (G.trajectory t : V) (v : V) * τ.toFun t := by
    rw [intervalIntegral.integral_of_le hab]
    exact integral_congr_ae (by filter_upwards [hG, hτ] with t hGt hτt; rw [hGt, hτt])
  have hforcing : (∫ t, ell t (v : V) * τ.toLp t ∂μab) =
      ∫ t in a..b, ell t (v : V) * τ.toFun t := by
    rw [intervalIntegral.integral_of_le hab]
    exact integral_congr_ae (by filter_upwards [hτ] with t hτt; rw [hτt])
  rw [htime, hform, hforcing]
  linarith

end L2DifferentiatedGalerkinApproximation

end PDE.Analysis.Evolution
