/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Interior.Estimates.Local
import PDE.FDeriv.SpaceTime
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Interior regularity and derivative estimates for a heat polynomial

A nonstationary quartic heat polynomial exercises both space and time
derivatives. Its values after time five may be replaced by an arbitrary
function. The hypotheses and conclusions concern only the closed-top domain,
so they hold whatever the future values are.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open PDE.Common
open scoped ContDiff

namespace PDE.Examples.Parabolic.Heat.Interior

open HeatEquation

/-- A quartic, nonstationary two-dimensional heat polynomial. -/
def polynomial (x : ℝ^2) (t : ℝ) : ℝ :=
  x 0 ^ 4 + 12 * t * x 0 ^ 2 + 12 * t ^ 2 + x 1 ^ 2 + 2 * t

/-- The same polynomial in time-first Euclidean coordinates. -/
def spacetimePolynomial (p : ℝ^3) : ℝ :=
  p 1 ^ 4 + 12 * p 0 * p 1 ^ 2 + 12 * p 0 ^ 2 + p 2 ^ 2 + 2 * p 0

/-- The computer algebra system proves the polynomial is smooth. -/
theorem contDiff_spacetimePolynomial : ContDiff ℝ ∞ spacetimePolynomial := by
  cas

/-- Joint regularity in the product coordinates used by the local theorem. -/
theorem contDiff_polynomial : ContDiff ℝ ∞ polynomial.uncurry := by
  have h := contDiff_spacetimePolynomial.comp
    ((contDiff_timeSpaceCons_uncurry 2).comp (contDiff_snd.prodMk contDiff_fst))
  simpa only [spacetimePolynomial, polynomial, Function.comp_def, Function.uncurry_def,
    show (1 : Fin 3) = (0 : Fin 2).succ from rfl,
    show (2 : Fin 3) = (1 : Fin 2).succ from rfl,
    timeSpaceCons_zero, timeSpaceCons_succ] using h

/-- The spatial Fréchet derivative. -/
def spatialGradient (p : ℝ^2 × ℝ) : ℝ^2 →L[ℝ] ℝ :=
  fderiv ℝ (fun x ↦ polynomial x p.2) p.1

/-- The spatial derivative of the spatial gradient. -/
def spatialHessian (p : ℝ^2 × ℝ) : ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ :=
  fderiv ℝ (fun x ↦ spatialGradient (x, p.2)) p.1

/-- The explicit time derivative used in the `C²,¹` hypotheses. -/
def timeDerivative (p : ℝ^2 × ℝ) : ℝ := 12 * p.1 0 ^ 2 + 24 * p.2 + 2

/-- Parameter-dependent differentiation gives joint continuity of the gradient. -/
theorem contDiff_spatialGradient : ContDiff ℝ ∞ spatialGradient :=
  (contDiff_polynomial.comp (contDiff_snd.prodMk contDiff_fst.snd)).fderiv
    contDiff_fst (by simp)

/-- The Hessian is jointly continuous as well. -/
theorem contDiff_spatialHessian : ContDiff ℝ ∞ spatialHessian :=
  (contDiff_spatialGradient.comp (contDiff_snd.prodMk contDiff_fst.snd)).fderiv
    contDiff_fst (by simp)

/-- The time derivative is continuous. -/
theorem continuous_timeDerivative : Continuous timeDerivative := by
  unfold timeDerivative
  fun_prop

/-- The computer algebra system computes the time derivative. -/
theorem hasDerivAt_polynomial (x : ℝ^2) (t : ℝ) :
    HasDerivAt (polynomial x) (timeDerivative (x, t)) t := by
  unfold polynomial timeDerivative
  cas

/-- The computer algebra system computes the spatial Laplacian. -/
theorem laplacian_polynomial (x : ℝ^2) (t : ℝ) :
    laplacian (fun y ↦ polynomial y t) x = timeDerivative (x, t) := by
  unfold polynomial timeDerivative
  cas

/-- The mixed order exercised below is nonzero in the first spatial direction. -/
theorem secondPartialDeriv_timeDerivative (x : ℝ^2) (t : ℝ) :
    (∂[0] (∂[0] (fun y ↦ timeDerivative (y, t)))) x = 24 := by
  change (∂[0] (fun y : ℝ^2 ↦
    (∂[0] ((fun z : ℝ^2 ↦ 12 * z 0 ^ 2 + 24 * t + 2) : ℝ^2 → ℝ)) y)) x = 24
  cas

/-- The heat residual vanishes. -/
theorem heatParabolicOperator_polynomial (x : ℝ^2) (t : ℝ) :
    heatParabolicOperator polynomial x t = 0 := by
  rw [heatParabolicOperator, (hasDerivAt_polynomial x t).deriv, laplacian_polynomial]
  exact sub_self _

/-- The heat polynomial up to time five, followed by arbitrary values `v`. The result may be
discontinuous at time five. -/
def withFuture (v : ℝ^2 → ℝ → ℝ) (x : ℝ^2) (t : ℝ) : ℝ :=
  if t ≤ 5 then polynomial x t else v x t

/-- All hypotheses hold for the polynomial with arbitrary future values. -/
theorem withFuture_raw_jets (v : ℝ^2 → ℝ → ℝ) :
    ContinuousOn (withFuture v).uncurry (univ ×ˢ Ioc 0 5) ∧
      ContinuousOn spatialGradient (univ ×ˢ Ioc 0 5) ∧
      ContinuousOn spatialHessian (univ ×ˢ Ioc 0 5) ∧
      ContinuousOn timeDerivative (univ ×ˢ Ioc 0 5) ∧
      (∀ p ∈ (univ : Set (ℝ^2)) ×ˢ Ioc 0 5,
        HasFDerivAt (fun y ↦ withFuture v y p.2) (spatialGradient p) p.1) ∧
      (∀ p ∈ (univ : Set (ℝ^2)) ×ˢ Ioc 0 5,
        HasFDerivAt (fun y ↦ spatialGradient (y, p.2)) (spatialHessian p) p.1) ∧
      (∀ p ∈ (univ : Set (ℝ^2)) ×ˢ Ioc 0 5,
        HasDerivWithinAt (withFuture v p.1) (timeDerivative p) (Ioc 0 5) p.2) ∧
      (∀ p ∈ (univ : Set (ℝ^2)) ×ˢ Ioc 0 5,
        timeDerivative p - laplacian (fun y ↦ withFuture v y p.2) p.1 = 0) := by
  refine ⟨?_, contDiff_spatialGradient.continuous.continuousOn,
    contDiff_spatialHessian.continuous.continuousOn,
    continuous_timeDerivative.continuousOn, ?_, ?_, ?_, ?_⟩
  · apply contDiff_polynomial.continuous.continuousOn.congr
    intro p hp
    simp only [Function.uncurry_def, withFuture, ite_eq_left hp.2.2]
  · intro p hp
    have h := (contDiff_polynomial.comp
      (contDiff_id.prodMk (contDiff_const (c := p.2)))).differentiable (by simp)
    simpa only [withFuture, ite_eq_left hp.2.2, spatialGradient,
      Function.comp_def, Function.uncurry_def, id_eq] using (h p.1).hasFDerivAt
  · intro p _
    exact ((contDiff_spatialGradient.comp
      (contDiff_id.prodMk contDiff_const)).differentiable (by simp) p.1).hasFDerivAt
  · intro p hp
    apply (hasDerivAt_polynomial p.1 p.2).hasDerivWithinAt.congr_of_mem _ hp.2
    intro s hs
    simp only [withFuture, ite_eq_left hs.2]
  · intro p hp
    simp only [withFuture, ite_eq_left hp.2.2, laplacian_polynomial, sub_self]

/-- Interior regularity: the solution is smooth on the closed-top domain, even when
the future values are arbitrary and possibly discontinuous. -/
theorem contDiffOn_withFuture (v : ℝ^2 → ℝ → ℝ) :
    ContDiffOn ℝ ∞ (withFuture v).uncurry (univ ×ˢ Ioc 0 5) := by
  obtain ⟨hu, hDx, hDxx, hDt, hx, hxx, ht, heq⟩ := withFuture_raw_jets v
  exact contDiffOn_of_heat_equation isOpen_univ hu hDx hDxx hDt hx hxx ht heq

/-- The theorem constructs a smooth extension across time five even though
the given future continuation is arbitrary. -/
theorem withFuture_terminal_extension (v : ℝ^2 → ℝ → ℝ) :
    ∃ (w : ℝ^2 × ℝ → ℝ) (W : Set (ℝ^2 × ℝ)),
      IsOpen W ∧ ((0 : ℝ^2), (5 : ℝ)) ∈ W ∧ ContDiffOn ℝ ∞ w W ∧
        EqOn (withFuture v).uncurry w (W ∩ (univ ×ˢ Ioc 0 5)) := by
  obtain ⟨hu, hDx, hDxx, hDt, hx, hxx, ht, heq⟩ := withFuture_raw_jets v
  exact exists_smooth_extension_of_heat_equation isOpen_univ hu hDx hDxx hDt
    hx hxx ht heq ⟨mem_univ _, by norm_num, le_rfl⟩

/-- A non-unit cylinder reaches the terminal time. The mixed derivative
with two spatial directions and one time direction has the exponent eight.
The same constant works for every arbitrary future continuation. -/
theorem withFuture_mixed_bound :
    ∃ C > 0, ∀ v : ℝ^2 → ℝ → ℝ,
      IntegrableOn (withFuture v).uncurry (closedBall 0 2 ×ˢ Icc 1 5) ∧
        ∀ p ∈ (closedBall (0 : ℝ^2) 1) ×ˢ Icc 4 5,
          ‖spaceTimeMixedFDerivWithin 2 1 (withFuture v).uncurry
            (univ ×ˢ Ioc 0 5) p‖ ≤
            C / 2 ^ 8 * ∫ q in (closedBall (0 : ℝ^2) 2) ×ˢ Icc 1 5,
              ‖withFuture v q.1 q.2‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_local_derivative_bound 2 2 1
  refine ⟨C, hC, fun v ↦ ?_⟩
  obtain ⟨hu, hDx, hDxx, hDt, hx, hxx, ht, heq⟩ := withFuture_raw_jets v
  have hcontain :
      closedBall (0 : ℝ^2) 2 ×ˢ Icc ((5 : ℝ) - 2 ^ 2) 5 ⊆ univ ×ˢ Ioc 0 5 := by
    intro p hp
    refine ⟨mem_univ _, ?_, hp.2.2⟩
    linarith [hp.2.1]
  have h := hbound univ 5 (withFuture v) spatialGradient spatialHessian timeDerivative
    isOpen_univ hu hDx hDxx hDt hx hxx ht heq 0 5 2 (by norm_num) hcontain
  norm_num only at h ⊢
  exact ⟨h.1, h.2.2⟩

end PDE.Examples.Parabolic.Heat.Interior
