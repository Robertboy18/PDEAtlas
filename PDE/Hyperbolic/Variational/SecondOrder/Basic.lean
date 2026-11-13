/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Second-order Carathéodory systems

We define second-order evolution equations with measurable
time-dependent stiffness,

`q''(t) + K(t)q(t) = f(t)`,

by rewriting them as first-order affine systems for `(q,q')`.  The
solution structure keeps the displacement and velocity separately and uses
absolute continuity with almost-everywhere equations, the natural regularity
for Bochner-integrable forcing.
-/

@[expose] public section

noncomputable section

open AbsolutelyContinuousOnInterval MeasureTheory Set
open scoped Topology

namespace Hyperbolic.Variational

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
The block operator for the first-order state `(q,p)` associated with
`q'' + K(t)q = f`.

It maps `(q,p)` to `(p,-K(t)q)`.  The forcing `(0,f(t))` is added separately,
so the resulting first-order equation is exactly
`(q',p') = (p,-K(t)q + f(t))`.
-/
def secondOrderStateOperator
    (K : ℝ → E →L[ℝ] E) (t : ℝ) : E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.snd ℝ E E).prod
    ((-(K t)).comp (ContinuousLinearMap.fst ℝ E E))

/-- The first-order state forcing corresponding to `q'' + K(t)q = f`. -/
def secondOrderStateForcing (f : ℝ → E) (t : ℝ) : E × E :=
  (0, f t)

/-- Unfolding the block operator: `(q, p) ↦ (p, -K(t) q)`. -/
@[simp]
theorem secondOrderStateOperator_apply (K : ℝ → E →L[ℝ] E) (t : ℝ) (z : E × E) :
    secondOrderStateOperator K t z = (z.2, -(K t) z.1) := by
  rfl

omit [NormedSpace ℝ E] in
/-- Unfolding the state forcing: the source `f(t)` enters only the velocity slot. -/
@[simp]
theorem secondOrderStateForcing_apply (f : ℝ → E) (t : ℝ) :
    secondOrderStateForcing f t = (0, f t) := by
  rfl

/--
A Carathéodory solution of

`q''(t) + K(t)q(t) = f(t),  q(a)=q₀,  q'(a)=p₀`

on `[a,b]`.  The displacement and velocity are ordinary Lean functions.
For measurable coefficients, absolute continuity and an almost-everywhere
equation are the correct regularity; the trajectory need not be `C²`.
-/
structure SecondOrderSolutionOn
    (K : ℝ → E →L[ℝ] E) (f : ℝ → E)
    (a b : ℝ) (q₀ p₀ : E) where
  /-- The displacement. -/
  displacement : ℝ → E
  /-- The velocity, equal almost everywhere to the derivative of
  `displacement`. -/
  velocity : ℝ → E
  /-- The prescribed initial displacement. -/
  initialDisplacement : displacement a = q₀
  /-- The prescribed initial velocity. -/
  initialVelocity : velocity a = p₀
  /-- The displacement is absolutely continuous in time. -/
  displacementAbsolutelyContinuous :
    AbsolutelyContinuousOnInterval displacement a b
  /-- The velocity is absolutely continuous in time. -/
  velocityAbsolutelyContinuous :
    AbsolutelyContinuousOnInterval velocity a b
  /-- The first state equation `q' = p` holds almost everywhere. -/
  displacementEquationAE :
    ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      HasDerivAt displacement (velocity t) t
  /-- The second state equation `p' = -K(t)q + f` holds almost everywhere. -/
  velocityEquationAE :
    ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      HasDerivAt velocity (-(K t) (displacement t) + f t) t

/--
The state operator is strongly measurable whenever the stiffness operator
is strongly measurable.
-/
theorem aestronglyMeasurable_secondOrderStateOperator {a b : ℝ} {K : ℝ → E →L[ℝ] E}
    (hK : AEStronglyMeasurable K (volume.restrict (Set.Icc a b))) :
    AEStronglyMeasurable (secondOrderStateOperator K) (volume.restrict (Set.Icc a b)) := by
  have hcontinuous : Continuous (fun L : E →L[ℝ] E ↦ (ContinuousLinearMap.snd ℝ E E).prod
            ((-L).comp (ContinuousLinearMap.fst ℝ E E))) := by
    have hright : Continuous (fun L : E →L[ℝ] E ↦ (-L).comp (ContinuousLinearMap.fst ℝ E E)) :=
      ((ContinuousLinearMap.compL ℝ (E × E) E E).flip
        (ContinuousLinearMap.fst ℝ E E)).continuous.comp continuous_neg
    exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp (continuous_const.prodMk hright)
  exact hcontinuous.comp_aestronglyMeasurable hK

/-- Integrability of the physical forcing implies integrability of the
corresponding product-space forcing. -/
theorem integrableOn_secondOrderStateForcing {a b : ℝ} {f : ℝ → E}
    (hf : IntegrableOn f (Set.Icc a b) volume) :
    IntegrableOn (secondOrderStateForcing f) (Set.Icc a b) volume := by
  let inr : E →L[ℝ] E × E := ContinuousLinearMap.inr ℝ E E
  have hcomp := inr.integrable_comp hf
  apply hcomp.congr
  filter_upwards with t
  rfl

/--
The block state operator is bounded by `1 + ‖K(t)‖`.  The estimate is
elementary: the first component is a projection and the second
is `K(t)` followed by a projection.
-/
theorem norm_secondOrderStateOperator_le (K : ℝ → E →L[ℝ] E) (t : ℝ) :
    ‖secondOrderStateOperator K t‖ ≤ 1 + ‖K t‖ := by
  rw [secondOrderStateOperator, ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  apply max_le
  · exact (ContinuousLinearMap.norm_snd_le ℝ E E).trans (le_add_of_nonneg_right (norm_nonneg _))
  · calc
      ‖(-(K t)).comp (ContinuousLinearMap.fst ℝ E E)‖
          ≤ ‖-(K t)‖ * ‖ContinuousLinearMap.fst ℝ E E‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖K t‖ * 1 := by
        rw [norm_neg]
        gcongr
        exact ContinuousLinearMap.norm_fst_le ℝ E E
      _ ≤ 1 + ‖K t‖ := by
        simp only [mul_one]
        linarith [norm_nonneg (K t)]

end Hyperbolic.Variational
