/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.Solution
public import PDE.Analysis.Evolution.Time.WeakDerivative.Basic
import PDE.Analysis.Evolution.Bochner.Duality

/-!
# Weak solutions of the abstract wave equation

We formulate weak solutions of the abstract second-order hyperbolic equation

`u'' + B(t) u = ell(t)` on `(a, b)`, `u(a) = q₀`, `u'(a) = p₀`,

posed on a Gelfand triple `V ↪ H ↪ V*` with `J : V → H` the pivot inclusion and
`J* : H → V*` its adjoint. This is the notion of weak solution for second-order hyperbolic
equations of Evans, §7.2.1, on a Gelfand triple, with the bilinear forms given by a
bounded measurable family `B : ℝ → V →L V*`. A solution
is a triple of Bochner classes, displacement `u ∈ L²(a, b; V)`, velocity in `L²(a, b; H)` and
acceleration in `L²(a, b; V*)`, tied together by two integrated identities against separated
tests `w ⊗ τ` (which carry the initial data) and by the spatial equation
`acceleration + B(t) u = ell` almost everywhere in `V*`.

## Main results

* `IsGelfandWeakWaveSolution`: the solution predicate. The clause `interval_nonempty : a < b`
  is included because every other clause is vacuous when `a = b`.
* `integrable_pivotVelocityTimeTest`: integrability of `⟪velocity(t), J w⟫_H φ(t)` for an `L²`
  scalar test `φ`, the Bochner-duality step reused whenever identities are subtracted.
* `equation_testAE`, `acceleration_eq_residualAE`: the almost-everywhere equation tested
  against `w ∈ V`, and its residual form `acceleration = ell - B(t) u`.
* `velocity_hasWeakTimeDerivativeOn`: the separated-test velocity identity is the ordinary
  `V*`-valued distributional derivative `d/dt (J* velocity) = acceleration` on `(a, b)`.

## Implementation notes

The predicate records only separated tests `w : V`, `τ : TimeTest a b`, because that is the
form the Galerkin equations deliver. `velocity_hasWeakTimeDerivativeOn` shows this loses
nothing: Hilbert reflexivity identifies functionals on `V*` with evaluation at some `w`, and
compact support of `τ` converts the restricted `(a, b]` integrals into Lebesgue integrals on the
open interval. Later regularization and integration-by-parts arguments use the standard
Banach-valued weak derivative and never see `TimeTest`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.1 (the definition of a weak solution).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

/--
Evans's weak solution of the abstract wave equation

`u_tt(t) + B(t)u(t) = ell(t)`

on `(a,b)`, with initial displacement `q₀ ∈ V` and initial velocity
`p₀ ∈ H`.

The first clause is the integrated equation `u_t = velocity`, viewed through
the pivot embedding `H ↪ V*`; it carries `u(a)=Jq₀`.  The second clause is
the integrated equation `velocity_t = acceleration`; it carries
`u_t(a)=p₀`.  The final clause is the spatial weak equation in `V*` almost
everywhere.
-/
structure IsGelfandWeakWaveSolution
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ}
    (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b)))
    (u : Lp V 2 (volume.restrict (Set.Ioc a b)))
    (velocity : Lp H 2 (volume.restrict (Set.Ioc a b)))
    (acceleration : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b)))
    (q₀ : V) (p₀ : H) : Prop where
  /-- The time interval is nonempty.  Without this hypothesis all
  almost-everywhere equations and endpoint identities are vacuous when
  `a = b`. -/
  interval_nonempty : a < b
  /-- Integrated displacement equation, including the initial displacement. -/
  displacementIdentity : IsGelfandIntegratedWeakSolution
      T (fun _ ↦ 0)
      (fun t ↦ T.pivotToDual (velocity t))
      u (T.inclusion q₀)
  /-- Integrated velocity equation, including the initial velocity. -/
  velocityIdentity : ∀ (w : V) (τ : TimeTest a b),
    -(∫ t,
        inner ℝ (velocity t) (T.inclusion w) * τ.derivToLp t
          ∂(volume.restrict (Set.Ioc a b))) =
      (∫ t, acceleration t w * τ.toLp t
        ∂(volume.restrict (Set.Ioc a b))) +
      inner ℝ p₀ (T.inclusion w) * τ.toFun a
  /-- Spatial weak equation in `V*`, almost everywhere in time. -/
  equationAE : ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
    acceleration t + B t (u t) = ell t

/-- A pivot-space velocity paired with a fixed energy-space test and an
`L²` scalar time test is integrable.

This elementary Bochner-duality lemma is used when subtracting weak-wave
identities.  Keeping it separate avoids rebuilding the same Riesz/`L²`
argument for the displacement and velocity equations. -/
theorem integrable_pivotVelocityTimeTest {V H : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] {μ : Measure ℝ}
    (T : GelfandTriple (V := V) (H := H)) (w : V) (φ : Lp ℝ 2 μ) (velocity : Lp H 2 μ) :
    Integrable (fun t ↦ inner ℝ (velocity t) (T.inclusion w) * φ t) μ := by
  have hinner := L2.integrable_inner (𝕜 := ℝ) φ ((innerSL ℝ (T.inclusion w)).compLpL 2 μ velocity)
  apply hinner.congr
  filter_upwards [ (innerSL ℝ (T.inclusion w)).coeFn_compLpL velocity] with t ht
  rw [ht]
  simp [innerSL_apply_apply, real_inner_comm, mul_comm]

namespace IsGelfandWeakWaveSolution

variable
  {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {a b : ℝ}
  {T : GelfandTriple (V := V) (H := H)}
  {B : ℝ → V →L[ℝ] StrongDual ℝ V}
  {ell : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
  {velocity : Lp H 2 (volume.restrict (Set.Ioc a b))}
  {acceleration : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {q₀ : V} {p₀ : H}

/--
Scalar-test form of the weak wave equation:

`u_tt(t)(w) + B(t)(u(t),w) = ell(t)(w)`.

This theorem is derived from the `V*` equality; it is not a second solution
definition.
-/
theorem equation_testAE (h : IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ∀ w : V, acceleration t w + B t (u t) w = ell t w := by
  filter_upwards [h.equationAE] with t ht using fun w ↦ DFunLike.congr_fun ht w

/--
Equivalent residual form of the almost-everywhere equation.  This is useful
when the acceleration is eliminated from estimates or compactness arguments.
-/
theorem acceleration_eq_residualAE
    (h : IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc a b), acceleration t = ell t - B t (u t) := by
  filter_upwards [h.equationAE] with t ht using eq_sub_of_add_eq ht

/--
The weak velocity identity is the ordinary `V*`-valued distributional
derivative

`d/dt (T.pivotToDual (velocity t)) = acceleration t`

on the open interval `(a,b)`.

The solution predicate initially records only separated tests
`w : V`, `τ : TimeTest a b`, because that is the form obtained directly from
the Galerkin equations.  This theorem removes that presentation detail:
Hilbert reflexivity identifies every functional on `V*` with evaluation at
some `w : V`, while compact support converts the restricted `(a,b]`
integrals into ordinary Lebesgue integrals.  Subsequent time-regularization
and integration-by-parts arguments can therefore use the standard
Banach-valued weak derivative without knowing about `TimeTest`.
-/
theorem velocity_hasWeakTimeDerivativeOn
    [CompleteSpace V] (h : IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀) :
    PDE.Analysis.Evolution.HasWeakTimeDerivativeOn (Set.Ioo a b)
      (fun t ↦ T.pivotToDual (velocity t)) (fun t ↦ acceleration t) := by
  refine ⟨by
      simpa only [Function.comp_def] using T.pivotToDual.locallyIntegrableOn_comp
        ((locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp velocity).locallyIntegrable
          (by norm_num))).mono_set Set.Ioo_subset_Ioc_self),
    (locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp acceleration).locallyIntegrable
      (by norm_num))).mono_set Set.Ioo_subset_Ioc_self, fun functional φ hφ _ hsupp ↦ ?_⟩
  obtain ⟨w, hw⟩ := exists_eq_evaluation_of_doubleDual functional
  let τ : TimeTest a b := TimeTest.ofContDiffSupported φ hφ hsupp
  have hτ := h.velocityIdentity w τ
  have h1 : (∫ t, acceleration t w * φ t ∂volume.restrict (Set.Ioc a b)) =
      ∫ t, acceleration t w * τ.toLp t ∂volume.restrict (Set.Ioc a b) :=
    integral_congr_ae (by
      filter_upwards [TimeTest.ofContDiffSupported_toLp_ae φ hφ hsupp] with t ht
      rw [ht])
  have h2 : (∫ t, inner ℝ (velocity t) (T.inclusion w) * deriv φ t ∂volume.restrict (Set.Ioc a b)) =
      ∫ t, inner ℝ (velocity t) (T.inclusion w) * τ.derivToLp t ∂volume.restrict (Set.Ioc a b) :=
    integral_congr_ae (by
      filter_upwards [TimeTest.ofContDiffSupported_derivToLp_ae φ hφ hsupp] with t ht
      rw [ht])
  have hφ0 (t : ℝ) (ht : t ∉ Set.Ioc a b) : φ t = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ ht (Set.Ioo_subset_Ioc_self (hsupp h))
  have hdφ0 (t : ℝ) (ht : t ∉ Set.Ioc a b) : deriv φ t = 0 :=
    Function.notMem_support.1 fun h ↦ ht (Set.Ioo_subset_Ioc_self (hsupp (support_deriv_subset h)))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc a b)
      (f := fun t ↦ functional (acceleration t) * φ t) fun t ht ↦ by rw [hφ0 t ht, mul_zero],
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc a b)
      (f := fun t ↦ functional (T.pivotToDual (velocity t)) * deriv φ t) fun t ht ↦ by
        rw [hdφ0 t ht, mul_zero]]
  have hτa : τ.toFun a = 0 := TimeTest.ofContDiffSupported_initial_zero φ hφ hsupp
  simpa only [hw, GelfandTriple.pivotToDual_apply, h1, h2, hτa, mul_zero, add_zero] using hτ.symm

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
