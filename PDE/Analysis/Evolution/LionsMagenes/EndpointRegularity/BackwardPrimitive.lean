/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.LionsMagenes.Basic.Primitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import PDE.Analysis.Evolution.LionsMagenes.Basic.WeakDerivative
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.ReflectedExtension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Backward Bochner primitives on finite intervals

Backward interval primitives of `L²` trajectories are realized in the same
Bochner space and identified through their weak derivatives. For the identity
Gelfand triple this gives a Hilbert-valued weak-time-derivative theorem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 4. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

section BackwardPrimitive

/--
The backward primitive of an `L²(a,b;X)` trajectory has weak derivative
`-f` on the open interval:

`d/dt (∫ r in t..s, f(r)) = -f(t)`.

The proof zero-extends the canonical `Lp` representative, applies the global
Banach-valued primitive theorem, and then removes the extension using local
almost-everywhere congruence.  Both endpoints of each primitive remain
strictly inside `(a,b)`, so no endpoint Dirac mass is introduced.
-/
theorem hasWeakTimeDerivativeOn_backwardTimePrimitive_L2
    {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {a b : ℝ}
    (f : Lp X 2 (volume.restrict (Set.Ioc a b)))
    {s : ℝ} (hs : s ∈ Set.Ioo a b) :
    HasWeakTimeDerivativeOn (Set.Ioo a b)
      (backwardTimePrimitive (fun r ↦ f r) s)
      (fun t ↦ -f t) := by
  have hf₀ : Integrable (intervalZeroExtension a b fun t ↦ f t) volume :=
    integrable_intervalZeroExtension ((Lp.memLp f).integrable (by norm_num))
  refine ((hasWeakTimeDerivativeOn_backwardTimePrimitive hf₀ s).mono (subset_univ _))
    |>.congr_ae_restrict measurableSet_Ioo ?_ ?_ <;>
    refine (ae_restrict_iff' measurableSet_Ioo).2 (.of_forall fun t ht ↦ ?_)
  · exact intervalIntegral_intervalZeroExtension_eq (f := fun r ↦ f r) ht hs
  · simp only [intervalZeroExtension, indicator_of_mem (Ioo_subset_Ioc_self ht)]

/--
The backward primitive of an `L²(a,b;X)` trajectory, as an element of the
same Bochner space.

The pointwise primitive is continuous on `[a,b]`, hence bounded there and
therefore square-integrable.  The hyperbolic uniqueness proof uses it with
ordinary `Lp` linearity and the Lions–Magenes representative theorem.
-/
noncomputable def backwardTimePrimitiveLp
    {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : ℝ}
    (f : Lp X 2 (volume.restrict (Set.Ioc a b)))
    (hab : a ≤ b) (s : ℝ) (hs : s ∈ Set.Icc a b) :
    Lp X 2 (volume.restrict (Set.Ioc a b)) :=
  (memLp_restrict_Ioc_of_continuousOn
    ((continuousOn_backwardTimePrimitive
      (intervalIntegrable_coeFn_L2_restrict_Ioc f hab)
      (Set.Icc_subset_uIcc hs)).mono
        Set.Icc_subset_uIcc)).toLp

/-- The `Lp` class of the backward primitive agrees almost everywhere with
the Bochner interval integral.  This identification is used when translating
an abstract weak-derivative identity back to the test function
`v(t) = ∫ₜˢ u(τ) dτ` of Evans §7.2.2, Theorem 4.
-/
theorem backwardTimePrimitiveLp_apply_ae
    {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : ℝ}
    (f : Lp X 2 (volume.restrict (Set.Ioc a b)))
    (hab : a ≤ b) (s : ℝ) (hs : s ∈ Set.Icc a b) :
    ((backwardTimePrimitiveLp f hab s hs :
        Lp X 2 (volume.restrict (Set.Ioc a b))) : ℝ → X) =ᵐ[
          volume.restrict (Set.Ioc a b)]
      backwardTimePrimitive (fun r ↦ f r) s :=
  (memLp_restrict_Ioc_of_continuousOn ((continuousOn_backwardTimePrimitive
    (intervalIntegrable_coeFn_L2_restrict_Ioc f hab) (Icc_subset_uIcc hs)).mono
      Icc_subset_uIcc)).coeFn_toLp

/--
The `L²` backward primitive has Gelfand weak derivative `-f` in the identity
Hilbert triple.

The derivative is stored in the dual space through the pointwise Riesz map.
For every fixed `v : X`, the proof reduces to the scalar absolutely
continuous function

`t ↦ ∫ₜˢ ⟪f(r),v⟫ dr`,

whose derivative is `-⟪f(t),v⟫` almost everywhere.  Integration by parts
against `TimeTest` then gives the Gelfand weak-derivative identity.  The two
`Lp` coercions are changed to their pointwise formulas only under
almost-everywhere integral congruences.
-/
theorem hasGelfandWeakTimeDerivativeOn_backwardTimePrimitiveLp
    {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {a b : ℝ}
    (f : Lp X 2 (volume.restrict (Set.Ioc a b)))
    (hab : a ≤ b) (s : ℝ) (hs : s ∈ Set.Icc a b) :
    HasGelfandWeakTimeDerivativeOn
      (GelfandTriple.identity X)
      (backwardTimePrimitiveLp f hab s hs)
      (rieszToDualLp (-f)) := by
  intro v τ hτa
  let z : ℝ → ℝ := fun t ↦ inner ℝ v (f t)
  let q : ℝ → ℝ := fun t ↦ -(∫ r in s..t, z r)
  have hf : IntervalIntegrable (fun t ↦ f t) volume a b :=
    intervalIntegrable_coeFn_L2_restrict_Ioc f hab
  have hz : IntervalIntegrable z volume a b :=
    ⟨(innerSL ℝ v).integrable_comp hf.1, (innerSL ℝ v).integrable_comp hf.2⟩
  have hqAC : AbsolutelyContinuousOnInterval q a b :=
    (absolutelyContinuousOnInterval_backwardTimePrimitive hz (Icc_subset_uIcc hs)).congr
      fun t _ ↦ intervalIntegral.integral_symm s t
  have hqDeriv : ∀ᵐ t ∂volume, t ∈ uIcc a b → HasDerivAt q (-z t) t := by
    filter_upwards [hz.ae_hasDerivAt_integral] with t ht htI
    exact (ht htI s (Icc_subset_uIcc hs)).neg
  -- integration by parts against the test function `τ`, which vanishes at `b`
  have hparts := hqAC.integral_mul_deriv_eq_deriv_mul (τ.absolutelyContinuousOnInterval hab)
  have hleft : (∫ t in a..b, q t * deriv τ.toFun t) = ∫ t in a..b, q t * τ.derivFun t :=
    intervalIntegral.integral_congr_ae <| .of_forall fun t ht ↦ by
      rw [(τ.hasDerivAt t (by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht)).deriv]
  have hright : (∫ t in a..b, deriv q t * τ.toFun t) = ∫ t in a..b, (-z t) * τ.toFun t := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hqDeriv] with t ht hmem
    rw [(ht (uIoc_subset_uIcc hmem)).deriv]
  rw [hleft, hright, τ.final_zero, hτa] at hparts
  simp only [mul_zero, sub_self] at hparts
  have hdualIntegral : (∫ t, rieszToDualLp (-f) t v * τ.toLp t ∂volume.restrict (Ioc a b)) =
      ∫ t in a..b, (-z t) * τ.toFun t := by
    rw [intervalIntegral.integral_of_le hab]
    refine integral_congr_ae ?_
    filter_upwards [rieszToDualLp_apply_ae (-f), Lp.coeFn_neg f, τ.memLp.coeFn_toLp]
      with t hdual hfneg hτ
    change τ.toLp t = τ.toFun t at hτ
    rw [hdual, hfneg, hτ]
    change inner ℝ (-f t) v * τ.toFun t = (-inner ℝ v (f t)) * τ.toFun t
    rw [inner_neg_left, real_inner_comm]
  have hprimitiveIntegral : (∫ t, inner ℝ ((GelfandTriple.identity X).inclusion
        (backwardTimePrimitiveLp f hab s hs t)) ((GelfandTriple.identity X).inclusion v) *
          τ.derivToLp t ∂volume.restrict (Ioc a b)) =
      ∫ t in a..b, q t * τ.derivFun t := by
    rw [intervalIntegral.integral_of_le hab]
    refine integral_congr_ae ?_
    filter_upwards [backwardTimePrimitiveLp_apply_ae f hab s hs,
      τ.derivMemLp.coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with t hprimitive hτ ht
    change τ.derivToLp t = τ.derivFun t at hτ
    rw [hprimitive, hτ, GelfandTriple.identity_inclusion_apply,
      GelfandTriple.identity_inclusion_apply]
    have hmap := ContinuousLinearMap.map_backwardTimePrimitive (innerSL ℝ v) (hf.mono_set
      (uIcc_subset_uIcc (Icc_subset_uIcc (Ioc_subset_Icc_self ht)) (Icc_subset_uIcc hs)))
    change inner ℝ v (backwardTimePrimitive (fun r ↦ f r) s t) =
      backwardTimePrimitive (fun r ↦ inner ℝ v (f r)) s t at hmap
    rw [real_inner_comm, hmap]
    exact congrArg (· * τ.derivFun t) (intervalIntegral.integral_symm s t)
  rw [hdualIntegral, hprimitiveIntegral]
  linarith

end BackwardPrimitive

end PDE.Analysis.Evolution
