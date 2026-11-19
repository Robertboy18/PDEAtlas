/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.CoefficientGeometry
public import PDE.Spaces.Sobolev.Boundary.Atlas.Cutoffs
import PDE.FDeriv.Calculus
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.ChangeOfVariables

/-!
# Boundary regularity: chart specialization

We specialise the matrix algebra of `CoefficientGeometry` to a boundary-flattening
chart `E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)`. The chart derivative matrix `Dᵢₖ(x) = ∂ᵢ Eₖ(x)`, the
inverse Jacobian weight `J(y) = |det D(E⁻¹)(y)|`, and the physical coefficient field `A` combine
into the flattened coefficient

`Ã(y) = J(y) · D(E⁻¹ y)ᵀ A(E⁻¹ y) D(E⁻¹ y)`,

which is the principal coefficient of the transformed operator in the boundary `H²` estimate.
It is Evans's (64) in step 8 of the proof of §6.3.2, Theorem 4, with the weight `J`: Evans's
straightening map has `|det DΦ| = 1`, so his formula has no weight. For a chart of a `C¹`
extension atlas the flattened coefficient is then glued to `β I` outside the compact chart core
with the atlas's canonical cutoff, giving a globally defined coefficient field
`extendedFlattenedPrincipalCoefficientAt` that agrees with `Ã` on the core and keeps the
ellipticity constant.

We also prove the change-of-variables identities for smooth functions:
the forcing term `∫ f φ` and the principal pairing `∫ ⟨A ∇v, ∇ψ⟩` over the chart source equal the
corresponding integrals over the chart target with the flattened coefficient and forcing, so a
smooth divergence-form weak identity on the physical patch transports to the flattened patch.
The Sobolev (nonsmooth) version is in `ChartWeakEquation`.

## Main results

* `chartDerivativeMatrix`, `inverseChartJacobianWeight`, `flattenedPrincipalCoefficientAt`,
  `flattenedForcing`: the transformed coefficient and forcing fields for a chart.
* `extendedFlattenedPrincipalCoefficientAt`,
  `extendedFlattenedPrincipalCoefficientAt_eq_on_KTarget`,
  `matrixEllipticLowerBound_extendedFlattenedPrincipalCoefficientAt`: the globally glued field,
  its agreement with the exact transformed coefficient on the chart core, and preservation of
  ellipticity.
* `integral_source_forcing_eq_integral_flattenedForcing`,
  `integral_source_principalPairing_comp_eq_integral_flattened`: change of variables for the
  forcing and principal terms of the weak equation.
* `smoothWeakEquation_flattened`: transport of a smooth divergence-form weak identity from a
  physical chart patch to flattened coordinates.
* `matrixEllipticLowerBound_flattenedAt`: pointwise ellipticity of the flattened coefficient from
  ellipticity of `A`, a lower bound on `J`, and a lower singular-value bound on `D`.

## Implementation notes

The derivative matrix is indexed with the input coordinate first and the flattened coordinate
second, so that `Dᵀ A D` appears without transposition conventions hidden in notation. All chart
quantities are total Lean functions; the analytic hypotheses (`C¹` chart and inverse,
differentiable solution and test function) are carried by the theorems that need them.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 8 of the proof of Theorem 4, (61)-(68),
  pp. 338-339.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open Filter MeasureTheory Set
open SobolevSpace.Boundary.C1ExtensionAtlas.DerivedCutoffs
open scoped BigOperators ENNReal Topology

namespace GraphSpace.BoundaryRegularity

variable {n : ℕ}

/-- Derivative matrix of a boundary-flattening chart, with input-coordinate
index first and flattened-coordinate index second. -/
def chartDerivativeMatrix
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (x : ℝ^n) (i k : Fin n) : ℝ :=
  (∂[i] (fun z ↦ E z k)) x

/-- Absolute Jacobian determinant of the inverse chart.  This is the density
factor in the physical-to-flattened change of variables. -/
def inverseChartJacobianWeight
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)) (y : ℝ^n) : ℝ :=
  |(fderiv ℝ (fun z ↦ E.symm z) y).det|

/-- The inverse-chart Jacobian weight is an absolute value, hence nonnegative. -/
theorem inverseChartJacobianWeight_nonneg
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)) (y : ℝ^n) :
    0 ≤ inverseChartJacobianWeight (n := n) E y :=
  abs_nonneg _

/-- Physical coefficient field transformed into flattened coordinates. -/
def flattenedPrincipalCoefficientAt
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (A : ℝ^n → Fin n → Fin n → ℝ)
    (y : ℝ^n) (k l : Fin n) : ℝ :=
  flattenedPrincipalCoefficient
    (inverseChartJacobianWeight (n := n) E y)
    (chartDerivativeMatrix (n := n) E (E.symm y))
    (A (E.symm y)) k l

/-- Global coefficient field associated with one boundary chart.  On the
compact chart core it is the exact transformed coefficient; away from the
core it is convexly joined to `β I` using the canonical unit-range smooth
cutoff. -/
def extendedFlattenedPrincipalCoefficientAt
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ) :
    ℝ^n → Fin n → Fin n → ℝ :=
  glueCoefficientField (n := n)
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
      (n := n) (Ω := Ω) i).toFun β
    (flattenedPrincipalCoefficientAt (n := n) (hΩ.chart i) A)

/-- On the compact chart core (the boundary support transported to the chart target), the
canonical cutoff equals `1`, so the glued coefficient field is exactly the transformed coefficient
`J · Dᵀ A D`. -/
theorem extendedFlattenedPrincipalCoefficientAt_eq_on_KTarget
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ)
    {y : ℝ^n}
    (hy : y ∈ Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupportInTarget
      (n := n) (Ω := Ω) i) :
    extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y =
      flattenedPrincipalCoefficientAt (n := n) (hΩ.chart i) A y := by
  apply glueCoefficientField_eq_of_cutoff_eq_one
  exact targetSupportCutoff_eq_one_on_boundarySupportInTarget
    (n := n) (Ω := Ω) i y hy

/-- Once chart geometry supplies ellipticity of the exact transformed
coefficient, the global chart coefficient has the same ellipticity constant. -/
theorem matrixEllipticLowerBound_extendedFlattenedPrincipalCoefficientAt
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β alpha : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ) (y : ℝ^n)
    (hβα : alpha ≤ β)
    (hA :
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
          (n := n) (Ω := Ω) i).toFun y ≠ 0 →
      MatrixEllipticLowerBound
        (flattenedPrincipalCoefficientAt (n := n) (hΩ.chart i) A y) alpha) :
    MatrixEllipticLowerBound
      (extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y) alpha := by
  have hη := Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff_mem_Icc
    (n := n) (Ω := Ω) i y
  exact matrixEllipticLowerBound_glueCoefficientField
    _ β alpha _ y hη.1 hη.2 hβα hA

/-- The right-hand side density after flattening `∫ f φ` to chart
coordinates. -/
def flattenedForcing
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (f : ℝ^n → ℝ) (y : ℝ^n) : ℝ :=
  inverseChartJacobianWeight (n := n) E y * f (E.symm y)

/-- Change of variables for the forcing term in the weak equation.  The test
function is written in flattened coordinates, so its physical representative
is `ψ ∘ E`. -/
theorem integral_source_forcing_eq_integral_flattenedForcing
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (f ψ : ℝ^n → ℝ) :
    (∫ x in E.source, f x * ψ (E x) ∂(volume : Measure (ℝ^n))) =
      ∫ y in E.target,
        flattenedForcing (n := n) E f y * ψ y ∂(volume : Measure (ℝ^n)) := by
  have hderiv : ∀ y ∈ E.target,
      HasFDerivAt (fun z ↦ E.symm z)
        (fderiv ℝ (fun z ↦ E.symm z) y) y := by
    intro y _
    exact (hEsymm.differentiable (by norm_num) y).hasFDerivAt
  have hchange :=
    SobolevSpace.WeakChangeOfVariables.integral_source_eq_integral_abs_det_fderiv_mul
      (n := n) (E := E)
      (E' := fun y ↦ fderiv ℝ (fun z ↦ E.symm z) y)
      hderiv (fun x ↦ f x * ψ (E x))
  rw [hchange]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem E.open_target.measurableSet] with y hy
  rw [E.right_inv hy]
  simp [flattenedForcing]
  ac_rfl

/-- Pointwise energy identity for the coefficient field induced by a
boundary chart. -/
theorem principalPairing_flattenedPrincipalCoefficientAt
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (A : ℝ^n → Fin n → Fin n → ℝ)
    (y : ℝ^n) (ξ η : Fin n → ℝ) :
    principalPairing
        (flattenedPrincipalCoefficientAt (n := n) E A y) ξ η =
      inverseChartJacobianWeight (n := n) E y *
        principalPairing (A (E.symm y))
          (Matrix.mulVec
            (chartDerivativeMatrix (n := n) E (E.symm y)) ξ)
          (Matrix.mulVec
            (chartDerivativeMatrix (n := n) E (E.symm y)) η) := by
  exact principalPairing_flattenedPrincipalCoefficient
    (n := n) (inverseChartJacobianWeight (n := n) E y)
    (chartDerivativeMatrix (n := n) E (E.symm y))
    (A (E.symm y)) ξ η

/-- Pointwise principal-part transformation for smooth functions.  The
physical representatives are `v ∘ E` and `ψ ∘ E`; after applying the chain
rule at `E.symm y`, their physical gradients are exactly the chart derivative
matrix-vector products appearing in `flattenedPrincipalCoefficientAt`.

This theorem fixes the index order needed by the divergence-form weak
equation before any integration or Sobolev-density argument is used. -/
theorem inverseChartJacobianWeight_mul_principalPairing_comp
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (A : ℝ^n → Fin n → Fin n → ℝ)
    (v ψ : ℝ^n → ℝ) (y : ℝ^n) (hy : y ∈ E.target)
    (hv : DifferentiableAt ℝ v y) (hψ : DifferentiableAt ℝ ψ y) :
    inverseChartJacobianWeight (n := n) E y *
        principalPairing (A (E.symm y))
          (fun j ↦ (∂[j]
            (fun x ↦ v (E x))) (E.symm y))
          (fun i ↦ (∂[i]
            (fun x ↦ ψ (E x))) (E.symm y)) =
      principalPairing
        (flattenedPrincipalCoefficientAt (n := n) E A y)
        (fun l ↦ (∂[l] v) y)
        (fun k ↦ (∂[k] ψ) y) := by
  let D := chartDerivativeMatrix (n := n) E (E.symm y)
  have hchart : DifferentiableAt ℝ (fun x ↦ E x) (E.symm y) :=
    hE.differentiable (by norm_num) (E.symm y)
  have hv' : DifferentiableAt ℝ v (E (E.symm y)) := by
    simpa only [E.right_inv hy] using hv
  have hψ' : DifferentiableAt ℝ ψ (E (E.symm y)) := by
    simpa only [E.right_inv hy] using hψ
  have hvgrad :
      (fun j ↦ (∂[j]
        (fun x ↦ v (E x))) (E.symm y)) =
        Matrix.mulVec D
          (fun l ↦ (∂[l] v) y) := by
    funext j
    rw [PDE.partialDeriv_comp (n := n) j v (fun x ↦ E x)
      (E.symm y) hv' hchart, E.right_inv hy]
    simp only [Matrix.mulVec, D, chartDerivativeMatrix]
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  have hψgrad :
      (fun i ↦ (∂[i]
        (fun x ↦ ψ (E x))) (E.symm y)) =
        Matrix.mulVec D
          (fun k ↦ (∂[k] ψ) y) := by
    funext i
    rw [PDE.partialDeriv_comp (n := n) i ψ (fun x ↦ E x)
      (E.symm y) hψ' hchart, E.right_inv hy]
    simp only [Matrix.mulVec, D, chartDerivativeMatrix]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hvgrad, hψgrad]
  exact (principalPairing_flattenedPrincipalCoefficientAt
    (n := n) E A y
    (fun l ↦ (∂[l] v) y)
    (fun k ↦ (∂[k] ψ) y)).symm

/-- Smooth principal-part change of variables for a boundary chart. This is
the integral identity that transports the principal term of the
divergence-form weak equation to flattened coordinates, as in step 8 of
Evans's proof of §6.3.2, Theorem 4. -/
theorem integral_source_principalPairing_comp_eq_integral_flattened
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (A : ℝ^n → Fin n → Fin n → ℝ)
    (v ψ : ℝ^n → ℝ)
    (hv : Differentiable ℝ v) (hψ : Differentiable ℝ ψ) :
    (∫ x in E.source,
        principalPairing (A x)
          (fun j ↦ (∂[j]
            (fun z ↦ v (E z))) x)
          (fun i ↦ (∂[i]
            (fun z ↦ ψ (E z))) x)
        ∂(volume : Measure (ℝ^n))) =
      ∫ y in E.target,
        principalPairing
          (flattenedPrincipalCoefficientAt (n := n) E A y)
          (fun l ↦ (∂[l] v) y)
          (fun k ↦ (∂[k] ψ) y)
        ∂(volume : Measure (ℝ^n)) := by
  have hderiv : ∀ y ∈ E.target,
      HasFDerivAt (fun z ↦ E.symm z)
        (fderiv ℝ (fun z ↦ E.symm z) y) y := by
    intro y _
    exact (hEsymm.differentiable (by norm_num) y).hasFDerivAt
  have hchange :=
    SobolevSpace.WeakChangeOfVariables.integral_source_eq_integral_abs_det_fderiv_mul
      (n := n) (E := E)
      (E' := fun y ↦ fderiv ℝ (fun z ↦ E.symm z) y)
      hderiv
      (fun x ↦ principalPairing (A x)
        (fun j ↦ (∂[j]
          (fun z ↦ v (E z))) x)
        (fun i ↦ (∂[i]
          (fun z ↦ ψ (E z))) x))
  rw [hchange]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem E.open_target.measurableSet] with y hy
  simpa only [inverseChartJacobianWeight] using
    (inverseChartJacobianWeight_mul_principalPairing_comp
      (n := n) E hE A v ψ y hy (hv y) (hψ y))

/-- Transport a smooth divergence-form weak equation from a physical chart
patch to flattened coordinates.  The hypothesis is the ordinary weak
identity for the physical representatives `v ∘ E` and `ψ ∘ E`; the
conclusion contains exactly the transformed coefficient and forcing fields.

The theorem uses the library's variational notion of weak solution and
derives from it the local flattened equation, the counterpart for differentiable
functions of Evans's (61) in step 8 of the proof of §6.3.2, Theorem 4. -/
theorem smoothWeakEquation_flattened
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (A : ℝ^n → Fin n → Fin n → ℝ)
    (f v ψ : ℝ^n → ℝ)
    (hv : Differentiable ℝ v) (hψ : Differentiable ℝ ψ)
    (hweak :
      (∫ x in E.source,
          principalPairing (A x)
            (fun j ↦ (∂[j]
              (fun z ↦ v (E z))) x)
            (fun i ↦ (∂[i]
              (fun z ↦ ψ (E z))) x)
          ∂(volume : Measure (ℝ^n))) =
        ∫ x in E.source, f x * ψ (E x)
          ∂(volume : Measure (ℝ^n))) :
    (∫ y in E.target,
        principalPairing
          (flattenedPrincipalCoefficientAt (n := n) E A y)
          (fun l ↦ (∂[l] v) y)
          (fun k ↦ (∂[k] ψ) y)
        ∂(volume : Measure (ℝ^n))) =
      ∫ y in E.target,
        flattenedForcing (n := n) E f y * ψ y
        ∂(volume : Measure (ℝ^n)) := by
  calc
    _ = ∫ x in E.source,
          principalPairing (A x)
            (fun j ↦ (∂[j]
              (fun z ↦ v (E z))) x)
            (fun i ↦ (∂[i]
              (fun z ↦ ψ (E z))) x)
          ∂(volume : Measure (ℝ^n)) :=
      (integral_source_principalPairing_comp_eq_integral_flattened
        (n := n) hE hEsymm A v ψ hv hψ).symm
    _ = ∫ x in E.source, f x * ψ (E x)
          ∂(volume : Measure (ℝ^n)) := hweak
    _ = ∫ y in E.target,
          flattenedForcing (n := n) E f y * ψ y
          ∂(volume : Measure (ℝ^n)) :=
      integral_source_forcing_eq_integral_flattenedForcing
        (n := n) hEsymm f ψ

/-- Pointwise energy identity for the coefficient field induced by a
boundary chart. -/
theorem principalEnergy_flattenedPrincipalCoefficientAt
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (A : ℝ^n → Fin n → Fin n → ℝ)
    (y : ℝ^n) (η : Fin n → ℝ) :
    principalEnergy
        (flattenedPrincipalCoefficientAt (n := n) E A y) η =
      inverseChartJacobianWeight (n := n) E y *
        principalEnergy (A (E.symm y))
          (Matrix.mulVec
            (chartDerivativeMatrix (n := n) E (E.symm y)) η) := by
  exact principalEnergy_flattenedPrincipalCoefficient
    (n := n) (inverseChartJacobianWeight (n := n) E y)
    (chartDerivativeMatrix (n := n) E (E.symm y))
    (A (E.symm y)) η

/-- Pointwise ellipticity of the physical matrix and quantitative lower
bounds for a chart imply pointwise ellipticity of the flattened
coefficient field. -/
theorem matrixEllipticLowerBound_flattenedAt
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (A : ℝ^n → Fin n → Fin n → ℝ)
    (y : ℝ^n) (J₀ α m : ℝ)
    (hJ₀ : 0 ≤ J₀)
    (hJ : J₀ ≤ inverseChartJacobianWeight (n := n) E y)
    (hα : 0 ≤ α)
    (hA : MatrixEllipticLowerBound (A (E.symm y)) α)
    (hD : HasGradientLowerBound
      (chartDerivativeMatrix (n := n) E (E.symm y)) m) :
    MatrixEllipticLowerBound
      (flattenedPrincipalCoefficientAt (n := n) E A y)
      (J₀ * α * m ^ 2) := by
  exact matrixEllipticLowerBound_flattened
    (n := n) (inverseChartJacobianWeight (n := n) E y)
    J₀ α m (chartDerivativeMatrix (n := n) E (E.symm y))
    (A (E.symm y)) hJ₀ hJ hα hA hD

end GraphSpace.BoundaryRegularity
end SobolevSpace
