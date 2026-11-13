/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Boundary regularity: coefficient geometry

Finite-dimensional linear algebra for the coefficient matrices of a divergence-form operator
`-∂ᵢ(aⁱʲ ∂ⱼ u)` under a change of coordinates. Two operations are needed in the boundary `H²`
argument (steps 8-9 of Evans's proof of §6.3.2, Theorem 4):

* Flattening. If `y = E(x)` is a boundary-straightening chart with derivative matrix
  `D = DE(x)` and inverse Jacobian weight `J = |det D(E⁻¹)(y)|`, then the transformed operator has
  principal coefficient `J · Dᵀ A D`. Uniform ellipticity is preserved quantitatively: a lower
  bound `J₀ ≤ J`, ellipticity constant `α` for `A`, and a lower singular-value bound `m` for `D`
  give ellipticity constant `J₀ α m²` for the flattened matrix.
* Gluing. The flattened coefficient is only defined on the chart target. To apply a half-space
  estimate it is joined to a constant elliptic matrix `β I` by a cutoff `χ ∈ [0, 1]`, as
  `χ A + (1 - χ) β I`. For `β ≥ α` this convex combination keeps the ellipticity constant `α`.

Everything here is pointwise algebra on `Fin n → Fin n → ℝ`; no measure theory or Sobolev
structure enters. The abstract statements are specialised to charts in `ChartCoefficients`.

## Main results

* `principalEnergy`, `principalPairing`, `MatrixEllipticLowerBound`: the quadratic form
  `∑ aⁱʲ ξᵢ ξⱼ`, the bilinear pairing in the index order of the weak equation, and the lower-bound
  relation `α |ξ|² ≤ ∑ aⁱʲ ξᵢ ξⱼ`.
* `glueToScalarIdentity`, `matrixEllipticLowerBound_glueToScalarIdentity`,
  `matrixEllipticLowerBound_glueCoefficientField`: convex gluing to `β I` and preservation of the
  ellipticity constant.
* `flattenedPrincipalCoefficient`, `flattenedPrincipalCoefficient_eq_matrix`: the transformed
  matrix `J · Dᵀ A D`.
* `principalPairing_flattenedPrincipalCoefficient`, `principalEnergy_flattenedPrincipalCoefficient`:
  the exact identities `⟨J Dᵀ A D ξ, η⟩ = J ⟨A (Dξ), Dη⟩` behind the change of variables.
* `matrixEllipticLowerBound_flattened`: quantitative preservation of ellipticity by a chart.

## Implementation notes

`MatrixEllipticLowerBound A α` does not require `α > 0`; positivity is a separate hypothesis in
the analytic theorems, so that the purely algebraic transport lemmas can be stated without it.
The index convention in `principalPairing A ξ η = ∑ aⁱʲ ξⱼ ηᵢ` puts the solution gradient in the
second index and the test gradient in the first, matching the library's weak divergence-form
equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, steps 8-9 of the proof of Theorem 4, (64) and
  (69)-(70), pp. 338-340.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace GraphSpace.BoundaryRegularity

variable {n : ℕ}

/-- Quadratic energy associated with a pointwise coefficient matrix. -/
def principalEnergy (A : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * ξ i * ξ j

/-- Bilinear principal pairing in the index order used by the weak
divergence-form equation: the solution derivative carries index `j`, and the
test derivative carries index `i`. -/
def principalPairing
    (A : Fin n → Fin n → ℝ) (ξ η : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * ξ j * η i

/--
Pointwise quadratic lower-bound relation for a finite coefficient matrix.

Positivity of `α` is a separate hypothesis in analytic
coercivity and regularity theorems. The algebraic transport and gluing lemmas
in this module need only the lower-bound relation itself.
-/
def MatrixEllipticLowerBound
    (A : Fin n → Fin n → ℝ) (α : ℝ) : Prop :=
  ∀ ξ, α * (ξ ⬝ᵥ ξ) ≤ principalEnergy A ξ

/-- Scalar multiple of the identity matrix, used to extend a locally
defined elliptic matrix away from a chart patch. -/
def scalarIdentityMatrix (β : ℝ) (i j : Fin n) : ℝ :=
  if i = j then β else 0

/-- The quadratic form of `β I` is `β |ξ|²`. -/
theorem principalEnergy_scalarIdentityMatrix (β : ℝ) (ξ : Fin n → ℝ) :
    principalEnergy (scalarIdentityMatrix (n := n) β) ξ =
      β * (ξ ⬝ᵥ ξ) := by
  classical
  simp only [principalEnergy, scalarIdentityMatrix, dotProduct]
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        (if i = j then β else 0) * ξ i * ξ j) =
        ∑ i : Fin n, β * ξ i * ξ i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Ne.symm hji]
      · simp
    _ = β * ∑ i : Fin n, ξ i * ξ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- Convexly glue a coefficient matrix to a scalar identity matrix. -/
def glueToScalarIdentity
    (χ β : ℝ) (A : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  χ * A i j + (1 - χ) * scalarIdentityMatrix (n := n) β i j

/-- The quadratic form of the glued matrix `χ A + (1 - χ) β I` is the same convex combination
`χ ⟨Aξ, ξ⟩ + (1 - χ) β |ξ|²` of the two quadratic forms. -/
theorem principalEnergy_glueToScalarIdentity
    (χ β : ℝ) (A : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    principalEnergy (glueToScalarIdentity (n := n) χ β A) ξ =
      χ * principalEnergy A ξ +
        (1 - χ) * β * (ξ ⬝ᵥ ξ) := by
  classical
  rw [show (1 - χ) * β * (ξ ⬝ᵥ ξ) =
      (1 - χ) * (β * (ξ ⬝ᵥ ξ)) by ring]
  rw [← principalEnergy_scalarIdentityMatrix (n := n) β ξ]
  simp only [principalEnergy, glueToScalarIdentity]
  simp_rw [add_mul, Finset.sum_add_distrib]
  have hleft :
      (∑ i : Fin n, ∑ j : Fin n, χ * A i j * ξ i * ξ j) =
        ∑ i : Fin n, χ * ∑ j : Fin n, A i j * ξ i * ξ j := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hright :
      (∑ i : Fin n, ∑ j : Fin n,
          (1 - χ) * scalarIdentityMatrix β i j * ξ i * ξ j) =
        ∑ i : Fin n, (1 - χ) * ∑ j : Fin n,
          scalarIdentityMatrix β i j * ξ i * ξ j := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hleft, hright, Finset.mul_sum, Finset.mul_sum]

/-- Gluing a matrix to `β I` with a cutoff in `[0,1]` preserves its quadratic
lower bound whenever `β ≥ alpha`. This is the coefficient extension used in
boundary-chart localization. -/
theorem matrixEllipticLowerBound_glueToScalarIdentity
    (χ β alpha : ℝ) (A : Fin n → Fin n → ℝ)
    (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) (hβα : alpha ≤ β)
    (hA : MatrixEllipticLowerBound A alpha) :
    MatrixEllipticLowerBound
      (glueToScalarIdentity (n := n) χ β A) alpha := by
  intro ξ
  have hnorm : 0 ≤ ξ ⬝ᵥ ξ := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (ξ i)
  have hAξ := hA ξ
  have hχA : χ * (alpha * (ξ ⬝ᵥ ξ)) ≤
      χ * principalEnergy A ξ := mul_le_mul_of_nonneg_left hAξ hχ0
  have honeχ : 0 ≤ 1 - χ := sub_nonneg.mpr hχ1
  have hid : (1 - χ) * (alpha * (ξ ⬝ᵥ ξ)) ≤
      (1 - χ) * (β * (ξ ⬝ᵥ ξ)) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hβα hnorm) honeχ
  rw [principalEnergy_glueToScalarIdentity]
  calc
    alpha * (ξ ⬝ᵥ ξ) =
        χ * (alpha * (ξ ⬝ᵥ ξ)) +
          (1 - χ) * (alpha * (ξ ⬝ᵥ ξ)) := by ring
    _ ≤ χ * principalEnergy A ξ +
        (1 - χ) * (β * (ξ ⬝ᵥ ξ)) := add_le_add hχA hid
    _ = χ * principalEnergy A ξ +
        (1 - χ) * β * (ξ ⬝ᵥ ξ) := by ring

/-- Pointwise coefficient field obtained by using a unit-range smooth cutoff
to glue the local matrix to `β I` away from the chart core. -/
def glueCoefficientField
    (η : ℝ^n → ℝ) (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ)
    (x : ℝ^n) : Fin n → Fin n → ℝ :=
  glueToScalarIdentity (n := n) (η x) β (A x)

/-- Where the cutoff equals `1`, the glued coefficient field is the original matrix field `A`. -/
theorem glueCoefficientField_eq_of_cutoff_eq_one
    (η : ℝ^n → ℝ) (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ)
    {x : ℝ^n} (hη : η x = 1) :
    glueCoefficientField (n := n) η β A x = A x := by
  funext i j
  simp [glueCoefficientField, glueToScalarIdentity, hη]

/-- Smooth convex gluing preserves the pointwise matrix lower bound. The range
hypotheses come from the cutoff constructor. -/
theorem matrixEllipticLowerBound_glueCoefficientField
    (η : ℝ^n → ℝ) (β alpha : ℝ)
    (A : ℝ^n → Fin n → Fin n → ℝ) (x : ℝ^n)
    (hη0 : 0 ≤ η x) (hη1 : η x ≤ 1)
    (hβα : alpha ≤ β)
    (hA : η x ≠ 0 → MatrixEllipticLowerBound (A x) alpha) :
    MatrixEllipticLowerBound
      (glueCoefficientField (n := n) η β A x) alpha := by
  by_cases hχ : η x = 0
  · intro ξ
    rw [show glueCoefficientField (n := n) η β A x =
        scalarIdentityMatrix (n := n) β by
      funext i j
      simp [glueCoefficientField, glueToScalarIdentity, hχ]]
    rw [principalEnergy_scalarIdentityMatrix]
    exact mul_le_mul_of_nonneg_right hβα (by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (ξ i))
  · exact matrixEllipticLowerBound_glueToScalarIdentity
      (η x) β alpha (A x) hη0 hη1 hβα (hA hχ)

/-- A quantitative lower singular-value bound for the chart derivative. -/
def HasGradientLowerBound
    (D : Fin n → Fin n → ℝ) (m : ℝ) : Prop :=
  ∀ η, m ^ 2 * (η ⬝ᵥ η) ≤
    Matrix.mulVec D η ⬝ᵥ Matrix.mulVec D η

/-- Principal coefficient matrix after flattening a divergence-form
operator.  The placement of the two chart derivatives is fixed by the weak
energy identity, rather than by a coordinate convention hidden in notation. -/
def flattenedPrincipalCoefficient
    (J : ℝ) (D A : Fin n → Fin n → ℝ) (k l : Fin n) : ℝ :=
  J * ∑ i, ∑ j, D i k * A i j * D j l

/-- The flattened coefficient is the matrix `J • (Dᵀ * A * D)`. -/
theorem flattenedPrincipalCoefficient_eq_matrix
    (J : ℝ) (D A : Matrix (Fin n) (Fin n) ℝ) :
    flattenedPrincipalCoefficient J D A =
      J • (Matrix.transpose D * A * D) := by
  classical
  funext k l
  simp only [flattenedPrincipalCoefficient, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- Exact bilinear identity for the flattened principal coefficient matrix.
This is the pointwise algebra underlying the transformed weak equation. -/
theorem principalPairing_flattenedPrincipalCoefficient
    (J : ℝ) (D A : Fin n → Fin n → ℝ) (ξ η : Fin n → ℝ) :
    principalPairing (flattenedPrincipalCoefficient J D A) ξ η =
      J * principalPairing A (Matrix.mulVec D ξ) (Matrix.mulVec D η) := by
  classical
  simp only [principalPairing, flattenedPrincipalCoefficient, Matrix.mulVec,
    dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_rhs =>
    enter [2, i, 2, j, 2, k]
    rw [Finset.mul_sum]
  conv_lhs =>
    enter [2, k]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, k, 2, i]
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, i]
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_congr rfl fun l _ ↦ by ring

/-- Exact energy identity for the flattened principal coefficient matrix.

This diagonal consequence checks both the transpose orientation and the
single inverse-Jacobian factor of the boundary-coordinate calculation. In
step 8 of Evans's proof of §6.3.2, Theorem 4, the factor is one, since
`|det DΦ| = 1`. -/
theorem principalEnergy_flattenedPrincipalCoefficient
    (J : ℝ) (D A : Fin n → Fin n → ℝ) (η : Fin n → ℝ) :
    principalEnergy (flattenedPrincipalCoefficient J D A) η =
      J * principalEnergy A (Matrix.mulVec D η) := by
  calc
    principalEnergy (flattenedPrincipalCoefficient J D A) η =
        principalPairing (flattenedPrincipalCoefficient J D A) η η := by
      unfold principalEnergy principalPairing
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ = J * principalPairing A (Matrix.mulVec D η) (Matrix.mulVec D η) :=
      principalPairing_flattenedPrincipalCoefficient (n := n) J D A η η
    _ = J * principalEnergy A (Matrix.mulVec D η) := by
      congr 1
      unfold principalEnergy principalPairing
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- Quantitative preservation of uniform ellipticity by a boundary chart.

If the inverse Jacobian weight is bounded below by `J₀`, and the derivative
matrix has lower singular bound `m`, then the flattened matrix has
ellipticity constant `J₀ * α * m²`. -/
theorem matrixEllipticLowerBound_flattened
    (J J₀ α m : ℝ) (D A : Fin n → Fin n → ℝ)
    (hJ₀ : 0 ≤ J₀) (hJ : J₀ ≤ J) (hα : 0 ≤ α)
    (hA : MatrixEllipticLowerBound A α)
    (hD : HasGradientLowerBound D m) :
    MatrixEllipticLowerBound
      (flattenedPrincipalCoefficient J D A) (J₀ * α * m ^ 2) := by
  intro η
  let ζ := Matrix.mulVec D η
  have hζη : m ^ 2 * (η ⬝ᵥ η) ≤ ζ ⬝ᵥ ζ := hD η
  have hζnonneg : 0 ≤ ζ ⬝ᵥ ζ := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (ζ i)
  have hAζ := hA ζ
  have henergyNonneg : 0 ≤ principalEnergy A ζ :=
    (mul_nonneg hα hζnonneg).trans hAζ
  rw [principalEnergy_flattenedPrincipalCoefficient]
  calc
    (J₀ * α * m ^ 2) * (η ⬝ᵥ η) =
        (J₀ * α) * (m ^ 2 * (η ⬝ᵥ η)) := by ring
    _ ≤ (J₀ * α) * (ζ ⬝ᵥ ζ) :=
      mul_le_mul_of_nonneg_left hζη (mul_nonneg hJ₀ hα)
    _ = J₀ * (α * (ζ ⬝ᵥ ζ)) := by ring
    _ ≤ J₀ * principalEnergy A ζ :=
      mul_le_mul_of_nonneg_left hAζ hJ₀
    _ ≤ J * principalEnergy A ζ :=
      mul_le_mul_of_nonneg_right hJ henergyNonneg

end GraphSpace.BoundaryRegularity
end SobolevSpace
