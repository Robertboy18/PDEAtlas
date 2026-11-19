/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Comparison.Locality
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.PositivePart

/-!
# Weak comparison for a shifted divergence-form equation

Consider `Lu = -∂ᵢ(aᵢⱼ ∂ⱼu) + bᵢ ∂ᵢu + cu` with real bounded measurable
coefficients. Testing the difference of two weak equations with `(u - v)⁺`
localizes every term of the form to `{u > v}`. The Gårding shift already used
to construct the resolvent then makes this test coercive. Ordered loads give
`u ≤ v` almost everywhere.

The argument uses the constructed positive part in the supported Sobolev
closure, including its weak derivative on the zero level set. It needs no
symmetry of the principal matrix, coefficient derivatives, boundedness of
the domain, or restriction on the spatial dimension. On measurable sets the
statement concerns the supported-core space; on open sets it is the usual
zero-boundary weak problem.

Locality matters: the comparison applies to multiplication coefficients,
whereas the underlying existence theorem also allows general bounded
operators on the derivative coordinates.

## Main statements

* `base_le_ae_of_isWeakSolution_shiftedDivergenceForm`: for every shift `mu` with
  `coerciveShift alpha beta gamma ≤ mu`, loads ordered on nonnegative `H¹₀` tests give
  ordered weak solutions.
* `shiftedDivergenceSolve_le_ae`: the resolvent `shiftedDivergenceSolve`, which uses the
  shift `coerciveShift alpha beta gamma`, preserves order in its scalar `L²` load when the
  divergence forcing is held fixed.
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open PDE.Analysis.Variational
open scoped ENNReal Topology InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

/-- Every coordinate of the positive part is localized to the positive set. -/
private theorem positivePart_coord_ae
    (hΩ : MeasurableSet Ω) (w : H¹₀(Ω)) (i : DerivIndex n 1) :
    (coordCLM i (positivePartWkp0 hΩ (by norm_num) w) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦
        if 0 < baseCoordCLM w x then coordCLM i w x else 0 := by
  rcases i.eq_baseIndex_or_eq_singleDerivIndex with hi | ⟨j, hi⟩
  · subst i
    have h := positivePartWkp0_base_ae hΩ (by norm_num) w
    change (baseCoordCLM (positivePartWkp0 hΩ (by norm_num) w) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦
        if 0 < baseCoordCLM w x then baseCoordCLM w x else 0
    change (baseCoordCLM (positivePartWkp0 hΩ (by norm_num) w) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ max (baseCoordCLM w x) 0 at h
    filter_upwards [h] with x hx
    rw [hx]
    split_ifs with hpos
    · exact max_eq_left hpos.le
    · exact max_eq_right (le_of_not_gt hpos)
  · subst i
    exact positivePartWkp0_derivative_ae hΩ (by norm_num) w j

/-- For `w ∈ H¹₀(Ω)`, testing the shifted form with `w⁺` gives its quadratic form at `w⁺`.
This is `interiorFullDivergenceOperator_positivePart_right` with `t = w⁺`. -/
theorem shiftedDivergenceForm_positivePart_right
    (hΩ : MeasurableSet Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (mu : ℝ) (w : H¹₀(Ω)) :
    shiftedDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c)
        mu w (positivePartWkp0 hΩ (by norm_num) w) =
      shiftedDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c)
        mu (positivePartWkp0 hΩ (by norm_num) w)
        (positivePartWkp0 hΩ (by norm_num) w) := by
  rw [shiftedDivergenceForm_apply, ← interiorFullDivergenceOperator_coe_H10]
  exact interiorFullDivergenceOperator_positivePart_right a b c mu
    (w : H¹(Ω)) (positivePartWkp0 hΩ (by norm_num) w)
    (positivePart_coord_ae hΩ w)

/-- If the positive part of a difference vanishes in the Sobolev space,
the original base coordinates are ordered almost everywhere. -/
private theorem base_le_of_positivePart_sub_eq_zero
    (hΩ : MeasurableSet Ω) (u v : H¹₀(Ω))
    (h : positivePartWkp0 hΩ (by norm_num) (u - v) = 0) :
    ∀ᵐ x ∂domainMeasure n Ω, baseCoordCLM u x ≤ baseCoordCLM v x := by
  have hp := positivePartWkp0_base_ae hΩ (by norm_num) (u - v)
  change (baseCoordCLM (positivePartWkp0 hΩ (by norm_num) (u - v)) : ℝ^n → ℝ)
    =ᵐ[domainMeasure n Ω] fun x ↦ max (baseCoordCLM (u - v) x) 0 at hp
  rw [h, map_zero, map_sub] at hp
  filter_upwards [hp, Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞))
    (μ := domainMeasure n Ω),
    Lp.coeFn_sub (baseCoordCLM u) (baseCoordCLM v)] with x hx hz hs
  change (0 : L2) x = max ((baseCoordCLM u - baseCoordCLM v) x) 0 at hx
  change (0 : L2) x = 0 at hz
  change (baseCoordCLM u - baseCoordCLM v) x =
    baseCoordCLM u x - baseCoordCLM v x at hs
  rw [hz, hs] at hx
  exact sub_nonpos.mp ((le_max_left _ _).trans_eq hx.symm)

/-- Ordered dual loads give ordered weak solutions of the shifted local equation.
Load order means inequality on every nonnegative zero-boundary test function.
The shift may be any value at least the Gårding coercivity threshold. -/
theorem base_le_ae_of_isWeakSolution_shiftedDivergenceForm
    (hΩ : MeasurableSet Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma mu : ℝ}
    (hA : IntegratedElliptic (multiplicationCoefficientOperator a) alpha)
    (hbc : LowerOrderBounds (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) beta gamma)
    (hmu : coerciveShift (n := n) alpha beta gamma ≤ mu)
    (ell₁ ell₂ : StrongDual ℝ H¹₀(Ω)) (u v : H¹₀(Ω))
    (hu : IsWeakSolution
      (shiftedDivergenceForm (n := n) (Ω := Ω) (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) mu)
      ell₁ u)
    (hv : IsWeakSolution
      (shiftedDivergenceForm (n := n) (Ω := Ω) (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) mu)
      ell₂ v)
    (hell : ∀ t : H¹₀(Ω), (∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM t x) →
      ell₁ t ≤ ell₂ t) :
    ∀ᵐ x ∂domainMeasure n Ω, baseCoordCLM u x ≤ baseCoordCLM v x := by
  let t : H¹₀(Ω) := positivePartWkp0 hΩ (by norm_num) (u - v)
  have ht : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM t x := by
    have hp := positivePartWkp0_base_ae hΩ (by norm_num) (u - v)
    change (baseCoordCLM t : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ max (baseCoordCLM (u - v) x) 0 at hp
    filter_upwards [hp] with x hx
    rw [hx]
    exact le_max_right _ _
  have hquad :
      shiftedDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) mu
        t t ≤ 0 := by
    rw [← shiftedDivergenceForm_positivePart_right hΩ a b c mu (u - v)]
    have heq := (hu.sub hv).apply t
    change shiftedDivergenceForm (multiplicationCoefficientOperator a)
      (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) mu
      (u - v) t = ell₁ t - ell₂ t at heq
    exact heq.le.trans (sub_nonpos.mpr (hell t ht))
  have hcoercive :=
    shiftedDivergenceForm_coercive_bound_of_coerciveShift_le
      (multiplicationCoefficientOperator a) (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) hA hbc hmu t
  have htzero : t = 0 := by
    apply norm_eq_zero.mp
    have hsq : ‖t‖ * ‖t‖ ≤ 0 := by
      apply le_of_mul_le_mul_left ?_ (half_pos hA.1)
      simpa only [mul_assoc, mul_zero] using hcoercive.trans hquad
    exact mul_self_eq_zero.mp (le_antisymm hsq (mul_self_nonneg _))
  exact base_le_of_positivePart_sub_eq_zero hΩ u v htzero

/-- Increasing the scalar part of `f₀ - div f` increases its value on every
nonnegative test function when the divergence part is unchanged. -/
private theorem generalizedLoad_le_of_ae_le
    (f₀ g₀ : L2) (f : Fin n → L2)
    (hfg : ∀ᵐ x ∂domainMeasure n Ω, f₀ x ≤ g₀ x)
    (t : H¹₀(Ω)) (ht : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM t x) :
    generalizedLoad f₀ f t ≤ generalizedLoad g₀ f t := by
  simp only [generalizedLoad_apply]
  apply add_le_add_left
  apply sub_nonpos.mp
  rw [← inner_sub_left, MeasureTheory.L2.inner_def]
  apply integral_nonpos_of_ae
  filter_upwards [hfg, ht, Lp.coeFn_sub f₀ g₀] with x hfgx htx hx
  change (f₀ - g₀) x = f₀ x - g₀ x at hx
  change inner ℝ ((f₀ - g₀) x) (baseCoordCLM t x) ≤ (0 : ℝ)
  rw [hx]
  simpa only [Real.inner_apply] using
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hfgx) htx

/-- The shifted resolvent preserves order in its scalar `L²` load,
with the divergence forcing held fixed. All coefficients are `L∞` multipliers. -/
theorem shiftedDivergenceSolve_le_ae
    (hΩ : MeasurableSet Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (multiplicationCoefficientOperator a) alpha)
    (hbc : LowerOrderBounds (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) beta gamma)
    (f₀ g₀ : L2) (f : Fin n → L2)
    (hfg : ∀ᵐ x ∂domainMeasure n Ω, f₀ x ≤ g₀ x) :
    ∀ᵐ x ∂domainMeasure n Ω,
      baseCoordCLM
        (shiftedDivergenceSolve (multiplicationCoefficientOperator a)
          (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c)
          hA hbc f₀ f) x ≤
      baseCoordCLM
        (shiftedDivergenceSolve (multiplicationCoefficientOperator a)
          (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c)
          hA hbc g₀ f) x := by
  apply base_le_ae_of_isWeakSolution_shiftedDivergenceForm hΩ a b c hA hbc le_rfl
    (generalizedLoad f₀ f) (generalizedLoad g₀ f) _ _
    (shiftedDivergenceSolve_isWeakSolution _ _ _ hA hbc f₀ f)
    (shiftedDivergenceSolve_isWeakSolution _ _ _ hA hbc g₀ f)
  exact generalizedLoad_le_of_ae_le f₀ g₀ f hfg

end SobolevSpace.GraphSpace
