/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.SecondOrder.Basic
public import PDE.Analysis.Evolution.ODE.Caratheodory.Affine
public import Mathlib.Analysis.Calculus.Deriv.Prod -- shake: keep
public import PDE.Analysis.Evolution.Time.AbsoluteContinuity -- shake: keep
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Well-posedness of second-order Carathéodory systems

Existence and uniqueness for the second-order affine system

`q''(t) + K(t) q(t) = f(t),  q(a) = q₀,  q'(a) = p₀`

on a compact interval `[a, b]`, in the Carathéodory sense of
`Hyperbolic.Variational.SecondOrderSolutionOn`: displacement and velocity are absolutely
continuous and the equations hold almost everywhere. The stiffness `K` is only required to be
almost everywhere strongly measurable and bounded on `[a, b]`, and the forcing `f` Bochner
integrable. This is the regularity in which the Galerkin coefficient systems of the weak wave
equation arise, since the coefficients `e^{kl}(t) = B[w_l, w_k; t]` inherit no more than
measurability in time from the operator coefficients and the projected data `f^k(t)` is merely
integrable. For finite-dimensional `E` this is the ODE step of the Galerkin existence proof
for second-order hyperbolic equations (Evans, §7.2.2, Theorem 1).

Both results are obtained by passing to the first-order state `z = (q, q')`, whose equation
`z' = A(t) z + F(t)` with `A(t) = secondOrderStateOperator K t` and
`F(t) = secondOrderStateForcing f t` is an affine Carathéodory system; the operator bound
`‖A(t)‖ ≤ 1 + ‖K(t)‖` from `norm_secondOrderStateOperator_le` converts a bound on `K` into
the bound the first-order theory needs.

## Main results

* `SecondOrderSolutionOn.exists`: global existence on `[a, b]` in any real Banach space `E`,
  with no smallness condition on the interval or on `K`.
* `SecondOrderSolutionOn.toAffineState`: a second-order solution as the
  corresponding `AffineCaratheodorySolutionOn` for the state `(q, q')`.
* `SecondOrderSolutionOn.eq_on`: uniqueness in any real Banach space `E`. Two solutions with
  the same data agree in displacement and velocity on all of `[a, b]`; the forcing cancels on
  subtraction, so only the bound on `K` is used.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, Theorem 1 and the linear ODE system (18) in its
  proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open AbsolutelyContinuousOnInterval MeasureTheory Set
open scoped Topology

namespace Hyperbolic.Variational

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/--
Global existence for a second-order affine system on a real Banach space with
a bounded measurable stiffness and integrable forcing.

The finite-dimensional Galerkin system needed in Evans's wave-equation
construction is an immediate specialization. No smallness assumption on the
interval or on the operator is imposed.
-/
theorem SecondOrderSolutionOn.exists {a b : ℝ} (hab : a ≤ b) (K : ℝ → E →L[ℝ] E) (f : ℝ → E)
    (hK : AEStronglyMeasurable K (volume.restrict (Set.Icc a b)))
    (hf : IntegrableOn f (Set.Icc a b) volume) (MK : NNReal)
    (hK_bound : ∀ t ∈ Set.Icc a b, ‖K t‖ ≤ MK) (q₀ p₀ : E) :
    Nonempty (SecondOrderSolutionOn K f a b q₀ p₀) := by
  let A : ℝ → E × E →L[ℝ] E × E := secondOrderStateOperator K
  let F : ℝ → E × E := secondOrderStateForcing f
  let MA : NNReal := 1 + MK
  have hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)) :=
    aestronglyMeasurable_secondOrderStateOperator hK
  have hF : IntegrableOn F (Set.Icc a b) volume := integrableOn_secondOrderStateForcing hf
  have hA_bound : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA := by
    intro t ht
    calc
      ‖A t‖ ≤ 1 + ‖K t‖ := norm_secondOrderStateOperator_le K t
      _ ≤ 1 + (MK : ℝ) := by gcongr; exact hK_bound t ht
      _ = (MA : ℝ) := rfl
  obtain ⟨U⟩ := PDE.Analysis.Evolution.AffineCaratheodorySolutionOn.exists
      hab A F hA hF MA hA_bound (q₀, p₀)
  let q : ℝ → E := fun t ↦ (U.trajectory t).1
  let p : ℝ → E := fun t ↦ (U.trajectory t).2
  have hqAC : AbsolutelyContinuousOnInterval q a b := by
    have h := (ContinuousLinearMap.fst ℝ E E).lipschitzWith.comp_absolutelyContinuousOnInterval
        U.absolutely_continuous
    refine h.congr fun t _ ↦ ?_
    rfl
  have hpAC : AbsolutelyContinuousOnInterval p a b := by
    have h := (ContinuousLinearMap.snd ℝ E E).lipschitzWith.comp_absolutelyContinuousOnInterval
        U.absolutely_continuous
    refine h.congr fun t _ ↦ ?_
    rfl
  have hqEq : ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt q (p t) t := by
    filter_upwards [U.equation_ae] with t ht
    have hproj := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t ht
    simpa [q, p, A, F, Function.comp_def,
      secondOrderStateOperator, secondOrderStateForcing] using! hproj
  have hpEq : ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt p (-(K t) (q t) + f t) t := by
    filter_upwards [U.equation_ae] with t ht
    have hproj := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t ht
    simpa [q, p, A, F, Function.comp_def,
      secondOrderStateOperator, secondOrderStateForcing] using! hproj
  exact ⟨{
    displacement := q
    velocity := p
    initialDisplacement := congrArg Prod.fst U.initial_value
    initialVelocity := congrArg Prod.snd U.initial_value
    displacementAbsolutelyContinuous := hqAC
    velocityAbsolutelyContinuous := hpAC
    displacementEquationAE := hqEq
    velocityEquationAE := hpEq
  }⟩

/--
View a second-order solution as the corresponding first-order affine
state solution.  This is used for the finite-dimensional Galerkin
trajectory; elsewhere displacement and velocity stay separate.
-/
def SecondOrderSolutionOn.toAffineState
    {K : ℝ → E →L[ℝ] E} {f : ℝ → E}
    {a b : ℝ} {q₀ p₀ : E}
    (U : SecondOrderSolutionOn K f a b q₀ p₀) :
    PDE.Analysis.Evolution.AffineCaratheodorySolutionOn
      (secondOrderStateOperator K) (secondOrderStateForcing f)
      a b (q₀, p₀) where
  trajectory := fun t ↦ (U.displacement t, U.velocity t)
  initial_value := Prod.ext U.initialDisplacement U.initialVelocity
  absolutely_continuous := by
    let z : ℝ → E × E := fun t ↦ (U.displacement t, U.velocity t)
    have hqEmbedded :
        AbsolutelyContinuousOnInterval
          (fun t ↦ (U.displacement t, (0 : E))) a b := by
      have h :=
        (ContinuousLinearMap.inl ℝ E E).lipschitzWith.comp_absolutelyContinuousOnInterval
          U.displacementAbsolutelyContinuous
      simpa only [Function.comp_def, ContinuousLinearMap.inl_apply] using! h
    have hpEmbedded :
        AbsolutelyContinuousOnInterval
          (fun t ↦ ((0 : E), U.velocity t)) a b := by
      have h :=
        (ContinuousLinearMap.inr ℝ E E).lipschitzWith.comp_absolutelyContinuousOnInterval
          U.velocityAbsolutelyContinuous
      simpa only [Function.comp_def, ContinuousLinearMap.inr_apply] using! h
    have hzAC : AbsolutelyContinuousOnInterval z a b := by
      have hsum := hqEmbedded.add hpEmbedded
      have hzEq :
          ((fun t ↦ (U.displacement t, (0 : E))) +
            fun t ↦ ((0 : E), U.velocity t)) = z := by
        funext t
        apply Prod.ext <;> simp [z]
      rw [← hzEq]
      exact hsum
    exact hzAC
  equation_ae := by
    filter_upwards [U.displacementEquationAE, U.velocityEquationAE] with t hq hp
    simpa [secondOrderStateOperator, secondOrderStateForcing] using hq.prodMk hp

/--
Uniqueness for the second-order Carathéodory problem in a Banach space.

Two solutions with the same displacement and velocity data agree in both
components throughout `[a,b]`.  The forcing needs no pointwise bound:
it cancels when the two equations are subtracted.  Only the measurable
bounded stiffness controls the resulting homogeneous difference equation.
-/
theorem SecondOrderSolutionOn.eq_on {a b : ℝ} (hab : a ≤ b) (K : ℝ → E →L[ℝ] E) (f : ℝ → E)
    (hK : AEStronglyMeasurable K (volume.restrict (Set.Icc a b))) (MK : NNReal)
    (hK_bound : ∀ t ∈ Set.Icc a b, ‖K t‖ ≤ MK) (q₀ p₀ : E)
    (U W : SecondOrderSolutionOn K f a b q₀ p₀) :
    ∀ t ∈ Set.Icc a b, U.displacement t = W.displacement t ∧ U.velocity t = W.velocity t := by
  let A : ℝ → E × E →L[ℝ] E × E := secondOrderStateOperator K
  let MA : NNReal := 1 + MK
  have hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)) :=
    aestronglyMeasurable_secondOrderStateOperator hK
  have hA_bound : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA := by
    intro t ht
    calc
      ‖A t‖ ≤ 1 + ‖K t‖ := norm_secondOrderStateOperator_le K t
      _ ≤ 1 + (MK : ℝ) := by
        gcongr
        exact hK_bound t ht
      _ = (MA : ℝ) := rfl
  have hstate := PDE.Analysis.Evolution.AffineCaratheodorySolutionOn.trajectory_eq
      hab hA MA hA_bound U.toAffineState W.toAffineState
  intro t ht
  have htState := hstate t ht
  exact ⟨congrArg Prod.fst htState, congrArg Prod.snd htState⟩

end Hyperbolic.Variational
