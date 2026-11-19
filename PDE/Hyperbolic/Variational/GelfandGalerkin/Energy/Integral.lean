/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.GelfandGalerkin.Energy.Basic
public import PDE.Analysis.Evolution.Galerkin.Gelfand.VectorField
public import PDE.Hyperbolic.Variational.SecondOrder.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import PDE.Analysis.Evolution.Core.EnergyIdentity
import PDE.Analysis.Evolution.Core.Gronwall
import PDE.Analysis.Evolution.Time.AbsoluteContinuity
import PDE.Hyperbolic.Variational.GelfandGalerkin.Basic

/-!
# Integrated Gelfand Galerkin wave energy

Energy estimates for a finite-dimensional Galerkin approximation of the abstract wave
equation `q'' + (A(t) + R(t)) q = ell(t)` posed on a Gelfand triple `V ↪ H ↪ V'`. The trajectory
is a `SecondOrderSolutionOn` for the projected operator `gelfandGalerkinOperator T S (A s + R s)`
on a finite-dimensional trial space `S ⊆ V`, so displacement and velocity are absolutely
continuous and the equations hold almost everywhere. The energy is Evans's

`E(t) = ½ ‖J q'(t)‖_H² + ½ A(t)(q(t), q(t))`,

with `J : V → H` the pivot inclusion (`gelfandWaveEnergy`). Only the symmetric principal form
`A` enters the energy; the lower-order form `R` is kept as a work term. This is the estimate
behind the Galerkin existence proof for second-order hyperbolic equations in Evans, §7.2.2,
for a time-dependent principal part and an absolutely continuous trajectory.

The identity is proved by absolute continuity: `E` is absolutely continuous on `[a, b]` because
each of its two terms is, and its almost-everywhere derivative is computed from the pointwise
derivative identity `hasDerivAt_gelfandWaveEnergy`. The fundamental theorem of calculus for
absolutely continuous functions then gives the integrated form.

## Main results

* `GelfandGalerkin.absolutelyContinuousOnInterval_gelfandWaveEnergy`: `E` is absolutely
  continuous on `[a, b]` whenever `A` is.
* `GelfandGalerkin.integratedEnergyIdentity`: for symmetric, absolutely continuous `A` with
  almost-everywhere derivative `Adot`,
  `E(t) - E(a) = ∫ₐᵗ [ell(q') - R(q, q') + ½ Adot(q, q)]` on `[a, b]`.
* `GelfandGalerkin.continuousOn_gelfandWaveEnergy`: continuity of `E` on `[a, b]`, the
  regularity the integral Grönwall lemma needs.
* `GelfandGalerkin.gelfandWaveEnergy_le_exp`: if the work integral is bounded by
  `G + Λ ∫ₐᵗ E` with `Λ ≥ 0`, then `E(t) ≤ (E(a) + G) exp(Λ (t - a))`.

## Implementation notes

The Grönwall theorem takes the work estimate `hwork` as a hypothesis, so the same statement
serves autonomous coefficients, variable principal parts, and equations
with lower-order terms; the Cauchy-Schwarz and Young steps that produce `G` and `Λ` are done
where the theorem is applied. None of the constants depend on the dimension of `S`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, Theorem 2 and its proof, equations (27)-(29).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open AbsolutelyContinuousOnInterval MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
Evans's Gelfand wave energy is absolutely continuous along an absolutely
continuous principal form and a second-order Galerkin trajectory.

The pivot kinetic term and the principal quadratic form are treated
separately.  This common regularity lemma supports both the integrated energy
identity and the continuity needed for Grönwall's inequality.
-/
theorem GelfandGalerkin.absolutelyContinuousOnInterval_gelfandWaveEnergy
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V) [FiniteDimensional ℝ S]
    [CompleteSpace S] (A : ℝ → V →L[ℝ] StrongDual ℝ V) {R : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : ℝ → StrongDual ℝ V} {a b : ℝ} {q₀ p₀ : S}
    (U : SecondOrderSolutionOn (fun s ↦ gelfandGalerkinOperator T S (A s + R s))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hAAC : AbsolutelyContinuousOnInterval A a b) :
    AbsolutelyContinuousOnInterval (gelfandWaveEnergy T S A U.displacement U.velocity) a b := by
  let J : S →L[ℝ] H := T.inclusion.comp S.subtypeL
  have hpHAC : AbsolutelyContinuousOnInterval (fun s ↦ J (U.velocity s)) a b := by
    simpa only [Function.comp_def] using!
      J.lipschitzWith.comp_absolutelyContinuousOnInterval U.velocityAbsolutelyContinuous
  have hqVAC : AbsolutelyContinuousOnInterval (fun s ↦ (U.displacement s : V)) a b := by
    simpa only [Function.comp_def] using!
      (S.subtypeL.lipschitzWith).comp_absolutelyContinuousOnInterval
        U.displacementAbsolutelyContinuous
  exact (((PDE.Analysis.Evolution.absolutelyContinuousOnInterval_norm_sq hpHAC).const_mul
    (1 / 2 : ℝ)).add ((PDE.Analysis.Evolution.AbsolutelyContinuousOnInterval.clm_apply
      (PDE.Analysis.Evolution.AbsolutelyContinuousOnInterval.clm_apply hAAC hqVAC)
        hqVAC).const_mul (1 / 2 : ℝ))).congr fun _ _ ↦ rfl

/--
Integrated Evans energy identity for a finite-dimensional Gelfand Galerkin
solution.

For the equation with full spatial form `A + R`, the identity is

`Eₘ(t) - Eₘ(a) = ∫ₐᵗ [ell(pₘ) - R(qₘ,pₘ)
  + 1/2 Adot(qₘ,qₘ)]`.

The hypotheses mirror the nonautonomous wave argument in Evans, §7.2.2:
the principal form is symmetric and absolutely continuous in time, while
the lower-order form appears as a separate work term, outside the positive
energy. The Galerkin equations hold almost everywhere.
-/
theorem GelfandGalerkin.integratedEnergyIdentity (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V) [FiniteDimensional ℝ S] [CompleteSpace S] (A R : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) {Adot : ℝ → V →L[ℝ] StrongDual ℝ V} {a b : ℝ} {q₀ p₀ : S}
    (U : SecondOrderSolutionOn (fun s ↦ gelfandGalerkinOperator T S (A s + R s))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ s ∂volume.restrict (Set.Ioc a b), HasDerivAt A (Adot s) s)
    (hA_symmetric : ∀ s ∈ Set.Icc a b, ∀ x y : V, A s x y = A s y x) :
    ∀ t ∈ Set.Icc a b,
      gelfandWaveEnergy T S A U.displacement U.velocity t -
          gelfandWaveEnergy T S A U.displacement U.velocity a =
        ∫ s in a..t, ell s (U.velocity s : V) - R s (U.displacement s : V) (U.velocity s : V) +
          (1 / 2 : ℝ) * Adot s (U.displacement s : V) (U.displacement s : V) := by
  have hderiv : ∀ᵐ s ∂volume.restrict (Set.Ioc a b),
      deriv (gelfandWaveEnergy T S A U.displacement U.velocity) s =
        ell s (U.velocity s : V) - R s (U.displacement s : V) (U.velocity s : V) +
          (1 / 2 : ℝ) * Adot s (U.displacement s : V) (U.displacement s : V) := by
    filter_upwards [hAderiv, U.displacementEquationAE,
      GelfandGalerkin.projectedEquationAE T S (fun s ↦ A s + R s) ell U,
      ae_restrict_mem measurableSet_Ioc] with s hAs hqs hps hs
    exact (hasDerivAt_gelfandWaveEnergy T S A R ell hAs hqs hps.1 hps.2
      (hA_symmetric s (Set.Ioc_subset_Icc_self hs))).deriv
  intro t ht
  rw [← ((GelfandGalerkin.absolutelyContinuousOnInterval_gelfandWaveEnergy T S A U hAAC).mono
    (uIcc_subset_uIcc_left (by rwa [uIcc_of_le hab]))).integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae_restrict ?_
  rw [uIoc_of_le ht.1]
  exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ht.2) hderiv

/--
Continuity of Evans's finite-dimensional Gelfand wave energy.

The coefficient curve `A` and both Galerkin trajectories are absolutely
continuous, hence continuous on the closed time interval.  Consequently the
pivot kinetic energy and the time-dependent principal energy are continuous.
This is the regularity needed to apply the integral form of Grönwall without
strengthening the Carathéodory trajectory to a `C²` solution.
-/
theorem GelfandGalerkin.continuousOn_gelfandWaveEnergy (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V) [FiniteDimensional ℝ S] [CompleteSpace S] (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    {R : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V} {a b : ℝ} {q₀ p₀ : S}
    (U : SecondOrderSolutionOn (fun s ↦ gelfandGalerkinOperator T S (A s + R s))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) (hAAC : AbsolutelyContinuousOnInterval A a b) :
    ContinuousOn (gelfandWaveEnergy T S A U.displacement U.velocity) (Set.Icc a b) := by
  simpa only [Set.uIcc_of_le hab] using
    (GelfandGalerkin.absolutelyContinuousOnInterval_gelfandWaveEnergy T S A U hAAC).continuousOn

/--
Integral Grönwall bound for the full nonautonomous Gelfand wave energy.

The exact energy identity leaves three work terms:

* forcing work `ell(p)`,
* lower-order work `-R(q,p)`, and
* coefficient work `Adot(q,q)/2`.

The hypothesis `hwork` is the integrated estimate obtained by applying
Cauchy-Schwarz and Young inequalities to those terms.  It keeps the full
work expression, so the theorem applies equally to
autonomous equations, variable principal coefficients, and equations with
lower-order terms.  Once

`∫ work ≤ G + Λ ∫ E`

has been established with `Λ ≥ 0`, Grönwall gives

`E(t) ≤ (E(a)+G) exp(Λ(t-a))`.

All constants are independent of the trial-space dimension.
-/
theorem GelfandGalerkin.gelfandWaveEnergy_le_exp (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V) [FiniteDimensional ℝ S] [CompleteSpace S] (A R : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) {Adot : ℝ → V →L[ℝ] StrongDual ℝ V} {a b : ℝ} {q₀ p₀ : S}
    (U : SecondOrderSolutionOn (fun s ↦ gelfandGalerkinOperator T S (A s + R s))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ s ∂volume.restrict (Set.Ioc a b), HasDerivAt A (Adot s) s)
    (hA_symmetric : ∀ s ∈ Set.Icc a b, ∀ x y : V, A s x y = A s y x) (Λ G : ℝ) (hΛ : 0 ≤ Λ)
    (hwork : ∀ t ∈ Set.Icc a b, (∫ s in a..t, ell s (U.velocity s : V) -
      R s (U.displacement s : V) (U.velocity s : V) + (1 / 2 : ℝ) *
      Adot s (U.displacement s : V) (U.displacement s : V)) ≤ G + Λ * ∫ s in a..t,
      gelfandWaveEnergy T S A U.displacement U.velocity s) :
    ∀ t ∈ Set.Icc a b, gelfandWaveEnergy T S A U.displacement U.velocity t ≤
      (gelfandWaveEnergy T S A U.displacement U.velocity a + G) * Real.exp (Λ * (t - a)) :=
  PDE.Analysis.Evolution.le_mul_exp_of_le_const_add_mul_intervalIntegral
    (GelfandGalerkin.continuousOn_gelfandWaveEnergy T S A U hab hAAC) hΛ fun t ht ↦ by
      linarith [GelfandGalerkin.integratedEnergyIdentity T S A R ell U hab hAAC hAderiv
        hA_symmetric t ht, hwork t ht]

end Hyperbolic.Variational
