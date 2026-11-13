/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical
public import PDE.Elliptic.Variational.Complex.FullForm

/-!
# Complex weak forms from smooth coefficients

The complex Sobolev graph and the coefficient `L∞` classes
define the complex full form. Its integral expression agrees with the
pointwise coefficient functions, and its real and imaginary parts agree
with the real form.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The complex weak full form from the same coefficient data as `form`. -/
def complexForm (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (U : ComplexWkSpaceOn n 1 Ω) (v : H¹₀(Ω)) : ℂ :=
  complexFullDivergenceForm
    (fun i j ↦ (P.principal_smooth 0 i j).toLp hopen hbounded ∞)
    (fun i ↦ (P.drift_smooth 0 i).toLp hopen hbounded ∞)
    ((P.potential_smooth 0).toLp hopen hbounded ∞) U v

/-- The complex form uses the coefficient values in every
integral; choosing their `L∞` representatives changes no term. -/
theorem complexForm_eq_integrals
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (U : ComplexWkSpaceOn n 1 Ω) (v : H¹₀(Ω)) :
    P.complexForm hopen hbounded U v =
      (∑ i, ∑ j, ∫ x, (P.principal x i j : ℂ) * U.1 (singleDerivIndex n j) x *
        (derivCoordCLM i v x : ℂ) ∂domainMeasure n Ω) +
      (∑ i, ∫ x, (P.drift i x : ℂ) * U.1 (singleDerivIndex n i) x *
        (baseCoordCLM v x : ℂ) ∂domainMeasure n Ω) +
      ∫ x, (P.potential x : ℂ) * U.1 (baseIndex n 1) x *
        (baseCoordCLM v x : ℂ) ∂domainMeasure n Ω := by
  unfold complexForm complexFullDivergenceForm
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [(P.principal_smooth 0 i j).toLp_coeFn hopen hbounded ∞] with x hx
    rw [hx]
  · apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [(P.drift_smooth 0 i).toLp_coeFn hopen hbounded ∞] with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [(P.potential_smooth 0).toLp_coeFn hopen hbounded ∞] with x hx
    rw [hx]

/-- A complex eigen-equation splits into the two real full
equations, with the signs determined by multiplication by the complex eigenvalue. -/
theorem parts_of_complexForm_eq
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (U : ComplexWkSpaceOn n 1 Ω)
    (hUr : U.re ∈ h10SubmoduleOn (n := n) (Ω := Ω))
    (hUi : U.im ∈ h10SubmoduleOn (n := n) (Ω := Ω))
    (lambda : ℂ) (v : H¹₀(Ω))
    (heq : P.complexForm hopen hbounded U v =
      lambda * ∫ x, U.1 (baseIndex n 1) x *
        (baseCoordCLM v x : ℂ) ∂domainMeasure n Ω) :
    P.form hopen hbounded ⟨U.re, hUr⟩ v =
      lambda.re * ⟪baseCoordCLM ⟨U.re, hUr⟩, baseCoordCLM v⟫_ℝ -
        lambda.im * ⟪baseCoordCLM ⟨U.im, hUi⟩, baseCoordCLM v⟫_ℝ ∧
    P.form hopen hbounded ⟨U.im, hUi⟩ v =
      lambda.re * ⟪baseCoordCLM ⟨U.im, hUi⟩, baseCoordCLM v⟫_ℝ +
        lambda.im * ⟪baseCoordCLM ⟨U.re, hUr⟩, baseCoordCLM v⟫_ℝ :=
  parts_of_complexFullDivergenceForm_eq _ _ _ U hUr hUi lambda v heq

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
