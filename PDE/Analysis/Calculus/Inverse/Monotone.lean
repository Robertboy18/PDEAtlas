/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Global inverses from a positive derivative lower bound

A differentiable real function whose derivative is bounded below by a positive
constant is an order isomorphism of the real line. Quantitative mean value
estimates prove surjectivity as well as the inverse Lipschitz bound. The
inverse is the inverse of this single order isomorphism, with its continuity
and inverse identities supplied by Mathlib.

Applying this construction to the derivative of a uniformly convex C² flux
requires no growth, range, or inverse assumptions.
-/

@[expose] public noncomputable section

open Set
open scoped NNReal

namespace PDE.Analysis

/-- A positive derivative lower bound forces a differentiable real function
to attain every real value. -/
theorem surjective_of_deriv_lower_bound
    {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {c : ℝ} (hc : 0 < c) (hderiv : ∀ x, c ≤ deriv f x) :
    Function.Surjective f := by
  intro y
  apply mem_range_of_exists_le_of_exists_ge hf.continuous
  · refine ⟨min 0 ((y - f 0) / c), ?_⟩
    have hmv := mul_sub_le_image_sub_of_le_deriv hf hderiv
      (min_le_left 0 ((y - f 0) / c))
    have ha := (le_div_iff₀ hc).1 (min_le_right 0 ((y - f 0) / c))
    linarith
  · refine ⟨max 0 ((y - f 0) / c), ?_⟩
    have hmv := mul_sub_le_image_sub_of_le_deriv hf hderiv
      (le_max_left 0 ((y - f 0) / c))
    have hb := (div_le_iff₀ hc).1 (le_max_right 0 ((y - f 0) / c))
    linarith

/-- A positive uniform lower bound on the derivative constructs an order
isomorphism of the real line, with forward function exactly the given map. -/
def orderIsoOfDerivLowerBound
    {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {c : ℝ} (hc : 0 < c) (hderiv : ∀ x, c ≤ deriv f x) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective f
    (strictMono_of_deriv_pos fun x ↦ hc.trans_le (hderiv x))
    (surjective_of_deriv_lower_bound hf hc hderiv)

/-- The constructed order isomorphism retains the original forward map. -/
@[simp] theorem coe_orderIsoOfDerivLowerBound
    {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {c : ℝ} (hc : 0 < c) (hderiv : ∀ x, c ≤ deriv f x) :
    ⇑(orderIsoOfDerivLowerBound hf hc hderiv) = f :=
  rfl

/-- The inverse has the reciprocal derivative. Its existence and continuity
come from the constructed order isomorphism. -/
theorem hasDerivAt_orderIsoOfDerivLowerBound_symm
    {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {c : ℝ} (hc : 0 < c) (hderiv : ∀ x, c ≤ deriv f x) (y : ℝ) :
    HasDerivAt (orderIsoOfDerivLowerBound hf hc hderiv).symm
      (deriv f ((orderIsoOfDerivLowerBound hf hc hderiv).symm y))⁻¹ y := by
  let e := orderIsoOfDerivLowerBound hf hc hderiv
  apply HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt
    (hf (e.symm y)).hasDerivAt (hc.trans_le (hderiv (e.symm y))).ne'
  exact Filter.Eventually.of_forall e.apply_symm_apply

/-- A continuously differentiable map with a positive derivative lower bound
has a continuously differentiable global inverse. -/
theorem contDiff_orderIsoOfDerivLowerBound_symm
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {c : ℝ} (hc : 0 < c) (hderiv : ∀ x, c ≤ deriv f x) :
    ContDiff ℝ 1 (orderIsoOfDerivLowerBound (hf.differentiable one_ne_zero) hc hderiv).symm := by
  let e := orderIsoOfDerivLowerBound (hf.differentiable one_ne_zero) hc hderiv
  have hd (y : ℝ) : HasDerivAt e.symm (deriv f (e.symm y))⁻¹ y :=
    hasDerivAt_orderIsoOfDerivLowerBound_symm (hf.differentiable one_ne_zero) hc hderiv y
  apply contDiff_one_iff_deriv.2
  refine ⟨fun y ↦ (hd y).differentiableAt, ?_⟩
  have heq : deriv e.symm = fun y ↦ (deriv f (e.symm y))⁻¹ :=
    funext fun y ↦ (hd y).deriv
  rw [heq]
  exact (hf.continuous_deriv_one.comp e.symm.continuous).inv₀
    fun y ↦ (hc.trans_le (hderiv (e.symm y))).ne'

/-- The inverse Lipschitz constant is the reciprocal of the derivative
lower bound. No upper bound on the derivative is needed. -/
theorem lipschitzWith_orderIsoOfDerivLowerBound_symm
    {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {c : ℝ} (hc : 0 < c) (hderiv : ∀ x, c ≤ deriv f x) :
    LipschitzWith (⟨c, hc.le⟩⁻¹ : ℝ≥0) (orderIsoOfDerivLowerBound hf hc hderiv).symm := by
  let e := orderIsoOfDerivLowerBound hf hc hderiv
  have hle {x y : ℝ} (hxy : x ≤ y) :
      dist (e.symm x) (e.symm y) ≤ c⁻¹ * dist x y := by
    have hmono := e.symm.monotone hxy
    have hmv := mul_sub_le_image_sub_of_le_deriv hf hderiv hmono
    have hx : f (e.symm x) = x := e.apply_symm_apply x
    have hy : f (e.symm y) = y := e.apply_symm_apply y
    rw [hx, hy] at hmv
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hmono),
      abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub, neg_sub]
    calc
      e.symm y - e.symm x ≤ (y - x) / c :=
        (le_div_iff₀ hc).2 (by simpa only [mul_comm] using hmv)
      _ = c⁻¹ * (y - x) := by rw [div_eq_mul_inv, mul_comm]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (e.symm x) (e.symm y) ≤ c⁻¹ * dist x y
  rcases le_total x y with hxy | hyx
  · exact hle hxy
  · simpa only [dist_comm] using hle hyx

end PDE.Analysis
