/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.H2
import PDE.Parabolic.Heat.Variational.Dirichlet -- shake: keep

/-!
# The autonomous form in higher parabolic regularity

We define the time-independent principal-part divergence-form operator
`autonomousDivergenceFormOperator` used for the `b = c = 0` case of Evans's §7.1.3,
Theorem 5, and prove two properties:

* coercivity on `H¹₀(Ω)`, from uniform ellipticity and Poincaré
  (`exists_autonomous_coercivity_constant`);
* symmetry, from symmetry of the pointwise coefficient matrix
  (`autonomous_divergence_form_operator_symmetric`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.1, (8) and the symmetry assumption, p. 373; §7.1.3,
  step 1 of the proof of Theorem 5 (Improved regularity), pp. 382-383.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set

namespace PDE.Parabolic.DivergenceFormHeat
namespace AutonomousRegularity

open PDE.Analysis.Evolution
open SobolevSpace
open SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal InnerProductSpace

variable {n : ℕ} [Fact (0 < n)]
variable {Ω : Set (ℝ^n)}

attribute [local instance 101] secondCountableTopologyEither_of_left

/--
The autonomous divergence-form operator associated with the Sobolev
coefficient matrix `A`.
-/
def autonomousDivergenceFormOperator
    (A : Fin n → Fin n → W^{1,∞}(Ω)) :
    H¹₀(Ω) →L[ℝ]
      StrongDual ℝ
        (H¹₀(Ω)) :=
  variableCoeffForm (n := n) (Ω := Ω)
    (multiplicationCoefficientOperator (n := n) (Ω := Ω)
      (coefficientBase A))

/--
Uniform ellipticity and the zero-trace Poincaré inequality produce a positive
coercivity constant for the autonomous divergence-form operator.
-/
theorem exists_autonomous_coercivity_constant
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Ω)
          (baseIndex n 1) : DerivLp n ∞ Ω)
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ C : ℝ, 0 < C ∧
      ∀ w : H¹₀(Ω),
        C * ‖w‖ ^ 2 ≤
          autonomousDivergenceFormOperator A w w := by
  let coeff := coefficientBase A
  have hAElliptic :
      AEUniformlyElliptic (n := n) (Ω := Ω) coeff alpha := by
    simpa only [coeff] using
      coefficientBase_aeUniformlyElliptic
        hΩ.toC1ExtensionAtlas.isOpen.measurableSet
        A a haRep alpha halpha hElliptic
  have hOpElliptic :
      IntegratedElliptic (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator
          (n := n) (Ω := Ω) coeff) alpha :=
    integratedElliptic_multiplication_of_ae
      (n := n) (Ω := Ω)
      coeff hAElliptic
  obtain ⟨C, hC, hcoercive⟩ :=
    variableCoeffForm_isCoercive
      (n := n) (Ω := Ω)
      (Fact.out : 0 < n) hΩ.toC1ExtensionAtlas.bounded
      (multiplicationCoefficientOperator
        (n := n) (Ω := Ω) coeff) hOpElliptic
  refine ⟨C, hC, ?_⟩
  intro w
  simpa only [autonomousDivergenceFormOperator, coeff, pow_two, mul_assoc] using
    hcoercive w

/--
Pointwise symmetry of a representative of `A` makes the autonomous
divergence-form operator symmetric on `H¹₀(Ω)`.

The proof transfers symmetry to the almost-everywhere coefficient operator
and then to the induced variational form. No ellipticity is needed.
-/
theorem autonomous_divergence_form_operator_symmetric
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Ω)
          (baseIndex n 1) : DerivLp n ∞ Ω)
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
    (haSymm : ∀ x ∈ Ω, ∀ i j, a x i j = a x j i)
    (v w : H¹₀(Ω)) :
    autonomousDivergenceFormOperator A v w =
      autonomousDivergenceFormOperator A w v := by
  have hAESymm :
      AESymmetricCoefficient (n := n) (Ω := Ω) (coefficientBase A) :=
    coefficientBase_aeSymmetric
      hΩ.toC1ExtensionAtlas.isOpen.measurableSet A a haRep haSymm
  exact variableCoeffForm_symm
    (n := n) (Ω := Ω)
    (symmetricCoefficientOperator_multiplication_of_ae
      (n := n) (Ω := Ω) (coefficientBase A) hAESymm) v w

end AutonomousRegularity
end PDE.Parabolic.DivergenceFormHeat
