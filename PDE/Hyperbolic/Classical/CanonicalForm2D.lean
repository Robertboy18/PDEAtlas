/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Canonical form of a two-variable hyperbolic equation

Evans, §7.2.5, considers the symmetric principal part

`a¹¹ uₓ₁ₓ₁ + 2 a¹² uₓ₁ₓ₂ + a²² uₓ₂ₓ₂`

of a linear second-order equation in two variables. Hyperbolicity is the
pointwise condition

`det A = a¹¹a²² - (a¹²)² < 0`.

The corresponding characteristic quadratic form factors over the reals.
Choosing two independent characteristic coordinates kills the two pure
second-derivative coefficients, leaving a nonzero mixed derivative. The
linear change

`z₁ = y₁ + y₂`, `z₂ = y₁ - y₂`

then converts that mixed derivative into a nonzero multiple of
`w_z₁z₁ - w_z₂z₂`.

We prove the pointwise principal-symbol algebra and the second-order
chain rule for the sum and difference change, equations (86)-(97) of Evans.
The derivative theorem requires only a `C²` germ of the transformed function.
Characteristic coordinates are constructed in `CanonicalForm2D.Chart`, and the full
equation with its lower-order terms is transformed in `CanonicalForm2D.Equation`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.5, equations (82)-(97).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace Hyperbolic.CanonicalForm2D

/--
A symmetric principal coefficient matrix in two variables,
written without duplicating its off-diagonal entry.
-/
structure PrincipalPart where
  /-- Coefficient of the pure second derivative in the first coordinate. -/
  a11 : ℝ
  /-- Half the mixed-derivative coefficient; the principal operator uses `2 * a12`. -/
  a12 : ℝ
  /-- Coefficient of the pure second derivative in the second coordinate. -/
  a22 : ℝ

namespace PrincipalPart

/-- Determinant of the symmetric principal coefficient matrix. -/
def determinant (A : PrincipalPart) : ℝ :=
  A.a11 * A.a22 - A.a12 ^ 2

/--
The positive-discriminant convention convenient for characteristic roots.
It is the negative of `determinant`.
-/
def discriminant (A : PrincipalPart) : ℝ :=
  A.a12 ^ 2 - A.a11 * A.a22

/--
The principal quadratic form evaluated on the covector `(xi1,xi2)`.
-/
def quadratic (A : PrincipalPart) (xi1 xi2 : ℝ) : ℝ :=
  A.a11 * xi1 ^ 2 +
    2 * A.a12 * xi1 * xi2 +
    A.a22 * xi2 ^ 2

/--
The symmetric polarization of `quadratic`, without the conventional factor
of two.  This is the transformed mixed coefficient associated with two
coordinate covectors.
-/
def mixed
    (A : PrincipalPart) (xi1 xi2 eta1 eta2 : ℝ) : ℝ :=
  A.a11 * xi1 * eta1 +
    A.a12 * (xi1 * eta2 + xi2 * eta1) +
    A.a22 * xi2 * eta2

/-- Determinant of the two covectors `(xi1,xi2)` and `(eta1,eta2)`. -/
def covectorDeterminant
    (xi1 xi2 eta1 eta2 : ℝ) : ℝ :=
  xi1 * eta2 - xi2 * eta1

/-- Evans's pointwise hyperbolicity condition `det A < 0`. -/
def IsHyperbolic (A : PrincipalPart) : Prop :=
  A.determinant < 0

/--
Evans's determinant condition is exactly positivity of the characteristic
discriminant.
-/
theorem isHyperbolic_iff_discriminant_pos (A : PrincipalPart) :
    A.IsHyperbolic ↔ 0 < A.discriminant := by
  simp only [IsHyperbolic, determinant, discriminant]
  constructor <;> intro h <;> linarith

/--
Evans equation (90): factorization of the characteristic quadratic form.

The expression is written without division by `a¹¹`, so the identity remains
valid even at points where that particular matrix entry vanishes.
-/
theorem characteristic_factorization (A : PrincipalPart) (xi1 xi2 : ℝ)
    (hdisc : 0 ≤ A.discriminant) :
    (A.a11 * xi1 + (A.a12 + Real.sqrt A.discriminant) * xi2) *
      (A.a11 * xi1 + (A.a12 - Real.sqrt A.discriminant) * xi2) = A.a11 * A.quadratic xi1 xi2 := by
  unfold discriminant at hdisc
  cas

/--
One characteristic covector obtained from the positive square-root branch.
-/
theorem quadratic_characteristicPlus (A : PrincipalPart) (hdisc : 0 ≤ A.discriminant) :
    A.quadratic (A.a12 + Real.sqrt A.discriminant) (-A.a11) = 0 := by
  have hsqrt : (Real.sqrt A.discriminant) ^ 2 = A.discriminant := Real.sq_sqrt hdisc
  calc
    A.quadratic (A.a12 + Real.sqrt A.discriminant) (-A.a11) = A.a11 *
          ((Real.sqrt A.discriminant) ^ 2 - A.discriminant) := by
      simp only [quadratic, discriminant]
      cas
    _ = 0 := by rw [hsqrt, sub_self, mul_zero]

/--
The second characteristic covector, from the negative square-root branch.
-/
theorem quadratic_characteristicMinus (A : PrincipalPart) (hdisc : 0 ≤ A.discriminant) :
    A.quadratic (A.a12 - Real.sqrt A.discriminant) (-A.a11) = 0 := by
  have hsqrt : (Real.sqrt A.discriminant) ^ 2 = A.discriminant := Real.sq_sqrt hdisc
  calc
    A.quadratic (A.a12 - Real.sqrt A.discriminant) (-A.a11) = A.a11 *
          ((Real.sqrt A.discriminant) ^ 2 - A.discriminant) := by
      simp only [quadratic, discriminant]
      cas
    _ = 0 := by rw [hsqrt, sub_self, mul_zero]

/--
The mixed coefficient produced by the two characteristic covectors.

This is the pointwise algebra behind Evans equation (94).  The displayed
normalization of the covectors gives the exact value
`-2 a¹¹ ((a¹²)²-a¹¹a²²)`.
-/
theorem mixed_characteristicPlus_characteristicMinus
    (A : PrincipalPart) (hdisc : 0 ≤ A.discriminant) :
    A.mixed (A.a12 + Real.sqrt A.discriminant) (-A.a11) (A.a12 - Real.sqrt A.discriminant)
      (-A.a11) = -2 * A.a11 * A.discriminant := by
  have hsqrt : (Real.sqrt A.discriminant) ^ 2 = A.discriminant := Real.sq_sqrt hdisc
  calc
    A.mixed (A.a12 + Real.sqrt A.discriminant) (-A.a11)
          (A.a12 - Real.sqrt A.discriminant) (-A.a11) = -A.a11 *
          (A.discriminant + (Real.sqrt A.discriminant) ^ 2) := by
      simp only [mixed, discriminant]
      cas
    _ = -2 * A.a11 * A.discriminant := by
      rw [hsqrt]
      cas

/--
For a hyperbolic principal part with `a¹¹ ≠ 0`, the two normalized
characteristic covectors have nonzero mixed coefficient.  Thus the
transformed principal part is mixed rather than degenerate.

The hypothesis `a¹¹ ≠ 0` is the normalization of the characteristic covectors used above.
-/
theorem mixed_characteristic_ne_zero (A : PrincipalPart) (hA11 : A.a11 ≠ 0)
    (hhyperbolic : A.IsHyperbolic) :
    A.mixed (A.a12 + Real.sqrt A.discriminant) (-A.a11) (A.a12 - Real.sqrt A.discriminant)
      (-A.a11) ≠ 0 := by
  have hdisc : 0 < A.discriminant := A.isHyperbolic_iff_discriminant_pos.mp hhyperbolic
  rw [A.mixed_characteristicPlus_characteristicMinus hdisc.le]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hA11) (ne_of_gt hdisc)

/--
Every hyperbolic symmetric principal part in two variables admits two
independent characteristic covectors whose mixed principal coefficient is
nonzero.

This is the chart-independent content needed for Evans equations
(87)-(95).  The proof covers both possibilities:

* if `a¹¹ ≠ 0`, use the two square-root branches above;
* if `a¹¹ = 0`, hyperbolicity forces `a¹² ≠ 0`, and the explicit covectors
  `(1,0)` and `(-a²²,2a¹²)` provide the two characteristic directions.
-/
theorem exists_independent_characteristicCovectors
    (A : PrincipalPart) (hhyperbolic : A.IsHyperbolic) :
    ∃ xi1 xi2 eta1 eta2 : ℝ, A.quadratic xi1 xi2 = 0 ∧ A.quadratic eta1 eta2 = 0 ∧
      A.mixed xi1 xi2 eta1 eta2 ≠ 0 ∧ covectorDeterminant xi1 xi2 eta1 eta2 ≠ 0 := by
  have hdisc : 0 < A.discriminant := A.isHyperbolic_iff_discriminant_pos.mp hhyperbolic
  by_cases hA11 : A.a11 = 0
  · have hA12 : A.a12 ≠ 0 := by
      intro hA12
      have : A.determinant = 0 := by
        simp [determinant, hA11, hA12]
      exact (ne_of_lt hhyperbolic) this
    refine ⟨1, 0, -A.a22, 2 * A.a12, ?_, ?_, ?_, ?_⟩
    · simp [quadratic, hA11]
    · simp only [quadratic, hA11, zero_mul, zero_add]
      cas
    · simp only [mixed, hA11, zero_mul, zero_add, mul_zero]
      simpa only [one_mul, add_zero, mul_assoc, mul_left_comm, mul_comm] using mul_ne_zero
          (mul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) hA12) hA12
    · simp only [covectorDeterminant]
      simpa only [one_mul, zero_mul, sub_zero] using
        mul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) hA12
  · refine ⟨A.a12 + Real.sqrt A.discriminant, -A.a11, A.a12 - Real.sqrt A.discriminant, -A.a11,
        A.quadratic_characteristicPlus hdisc.le, A.quadratic_characteristicMinus hdisc.le,
        A.mixed_characteristic_ne_zero hA11 hhyperbolic, ?_⟩
    have hsqrt : Real.sqrt A.discriminant ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdisc)
    have hdet : covectorDeterminant (A.a12 + Real.sqrt A.discriminant) (-A.a11)
            (A.a12 - Real.sqrt A.discriminant) (-A.a11) =
          -2 * A.a11 * Real.sqrt A.discriminant := by
      simp only [covectorDeterminant]
      cas
    rw [hdet]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hA11) hsqrt

end PrincipalPart

/-! ## From the mixed form to the wave form -/

/--
The principal expression in coordinates whose symmetric coefficient entries
are `b11`, `b12`, and `b22`.
-/
def principalExpression
    (b11 b12 b22 v11 v12 v22 : ℝ) : ℝ :=
  b11 * v11 + 2 * b12 * v12 + b22 * v22

/--
If both transformed coordinate covectors are characteristic, the two pure
coefficients vanish and only the mixed second derivative remains.
-/
theorem principalExpression_zero_pure (b12 v11 v12 v22 : ℝ) :
    principalExpression 0 b12 0 v11 v12 v22 = 2 * b12 * v12 := by
  simp [principalExpression]

/-- The linear change from characteristic coordinates to wave coordinates. -/
noncomputable def sumDifferenceCoordinates (y : ℝ^2) : ℝ^2 :=
  !₂[y 0 + y 1, y 0 - y 1]

private theorem contDiff_sumDifferenceCoordinates :
    ContDiff ℝ 2 sumDifferenceCoordinates := by
  refine (contDiff_piLp (p := (2 : ENNReal))).2 ?_
  intro i
  fin_cases i
  · change ContDiff ℝ 2 (fun y : ℝ^2 ↦ y 0 + y 1)
    cas
  · change ContDiff ℝ 2 (fun y : ℝ^2 ↦ y 0 - y 1)
    cas

/-- For `v(y) = w(y₀+y₁, y₀-y₁)`, the mixed derivative of `v` is the wave
operator applied to `w`. A `C²` germ supplies both the chain rule and symmetry
of the mixed derivatives. -/
theorem mixedDerivative_under_sumDifferenceCoordinates (w : ℝ^2 → ℝ) (y : ℝ^2)
    (hw : ContDiffAt ℝ 2 w (sumDifferenceCoordinates y)) :
    (∂[0] (∂[1] (w ∘ sumDifferenceCoordinates))) y = (∂[0] (∂[0] w)) (sumDifferenceCoordinates y) -
      (∂[1] (∂[1] w)) (sumDifferenceCoordinates y) := by
  have hfirst (i j : Fin 2) (x : ℝ^2) : (∂[i] (fun z ↦ sumDifferenceCoordinates z j)) x =
        if i = 1 ∧ j = 1 then -1 else 1 := by
    fin_cases i <;> fin_cases j
    · change (∂[0] (fun y : ℝ^2 ↦ y 0 + y 1)) x = 1
      cas
    · change (∂[0] (fun y : ℝ^2 ↦ y 0 - y 1)) x = 1
      cas
    · change (∂[1] (fun y : ℝ^2 ↦ y 0 + y 1)) x = 1
      cas
    · change (∂[1] (fun y : ℝ^2 ↦ y 0 - y 1)) x = -1
      cas
  have hchain := PDE.partialDeriv_partialDeriv_comp_at 0 1 w sumDifferenceCoordinates y
    hw contDiff_sumDifferenceCoordinates.contDiffAt
  simp only [Fin.isValue, hfirst, zero_ne_one, false_and, ↓reduceIte, mul_one,
    true_and, mul_ite, mul_neg, Finset.sum_ite_irrel, Finset.sum_neg_distrib,
    Fin.sum_univ_two, neg_add_rev, PDE.partialDeriv_const, mul_zero,
    Finset.sum_const_zero, add_zero] at hchain
  have hcomm := PDE.partialDeriv_partialDeriv_comm_at 0 1 hw
  change (∂[0] (∂[1] (w ∘ sumDifferenceCoordinates))) y = _ at hchain
  rw [hchain, hcomm]
  ring

/--
The principal differential expression after the sum/difference coordinate change.

After characteristic coordinates eliminate the pure `y` derivatives, the
sum/difference coordinate change sends the remaining mixed principal part
to a nonzero scalar multiple of the one-dimensional wave operator.  The
factor `2*b12` is retained rather than silently normalized away.
-/
theorem mixedPrincipalExpression_to_wave (b12 : ℝ) (w : ℝ^2 → ℝ) (y : ℝ^2)
    (hw : ContDiffAt ℝ 2 w (sumDifferenceCoordinates y)) :
    principalExpression 0 b12 0
        ((∂[0] (∂[0] (w ∘ sumDifferenceCoordinates))) y)
        ((∂[0] (∂[1] (w ∘ sumDifferenceCoordinates))) y)
        ((∂[1] (∂[1] (w ∘ sumDifferenceCoordinates))) y) =
      2 * b12 *
        ((∂[0] (∂[0] w)) (sumDifferenceCoordinates y) -
          (∂[1] (∂[1] w)) (sumDifferenceCoordinates y)) := by
  rw [principalExpression_zero_pure, mixedDerivative_under_sumDifferenceCoordinates w y hw]

end Hyperbolic.CanonicalForm2D
