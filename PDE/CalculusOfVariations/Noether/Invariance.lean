/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.ParameterDerivative
public import PDE.Analysis.Matrix.Determinant.Derivative
public import PDE.CalculusOfVariations.Noether.Current

/-!
# Invariant variations and Noether conservation

Let `U t` be a transformed field in the new spatial coordinates, and let `Φ t` map
the original spatial point to the new one. The pulled-back density is
`L(D(U t)(Φ t x), U t (Φ t x), Φ t x) det D(Φ t)(x)`.
Invariance means equality of these densities near `t = 0`.

We differentiate this equality, including its determinant factor, and combine it with
the pointwise first-variation identity. A classical Euler–Lagrange solution therefore
has a divergence-free Noether current. The dimensions of both domain and target are
arbitrary finite natural numbers. Regularity is local: the density is `C²` at the first
jet, and the two families are jointly `C²` at `(0, x)`. No ambient smooth extension
is required. Invariance and the Euler–Lagrange equations are needed only at `x`.

This is the invariant-variation form of Noether's theorem, Evans, §8.6.2, Theorem 1 (ii),
with the integral invariance (6) of §8.6.1 replaced by pointwise invariance of the density.
No group law is needed. The signed determinant is the usual volume factor near the
identity, where it is positive.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.6.1 and §8.6.2, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Elementwise Topology

namespace PDE.CalculusOfVariations.Noether

open Analysis

variable {n m : ℕ}

/-- The Lagrangian density of a transformed field, pulled back by the spatial transformation.
Both the field gradient and the volume factor are Jacobian matrices. -/
def transformedDensity (L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ)
    (U : ℝ → ℝ^n → ℝ^m) (Φ : ℝ → ℝ^n → ℝ^n) (t : ℝ) (x : ℝ^n) : ℝ :=
  fieldDensity L (U t) (Φ t x) * (jacobianMatrix (Φ t) x).det

variable {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
  {U : ℝ → ℝ^n → ℝ^m} {Φ : ℝ → ℝ^n → ℝ^n} {x : ℝ^n}

/-- The first variation of the spatial volume factor is the divergence of the spatial
velocity. This follows by differentiating the determinant at the identity matrix. -/
theorem hasDerivAt_spatial_volume
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id) :
    HasDerivAt (fun t ↦ (jacobianMatrix (Φ t) x).det)
      (∇· (fun y ↦ deriv (fun t ↦ Φ t y) 0) x) 0 := by
  have h := (Analysis.Matrix.hasFDerivAt_det (jacobianMatrix (Φ 0) x)).comp_hasDerivAt
    0 (hasDerivAt_jacobianMatrix hΦ)
  have hidentity : jacobianMatrix (Φ 0) x = 1 := by
    rw [jacobianMatrix_eq_of_eventuallyEq hΦ₀]
    exact jacobianMatrix_id x
  apply h.congr_deriv
  rw [hidentity]
  change Analysis.Matrix.detDerivative (1 : Matrix (Fin n) (Fin n) ℝ)
    (jacobianMatrix (fun y ↦ deriv (fun s ↦ Φ s y) 0) x) = _
  rw [Analysis.Matrix.detDerivative_apply, Matrix.adjugate_one]
  simp [Matrix.one_apply, divergence, jacobianMatrix, jacobianColumn]

/-- The density of a jointly `C²` family germ is jointly `C¹`. -/
theorem contDiffAt_family_fieldDensity {t : ℝ}
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U t) x, (U t x, x)))
    (hU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (t, x)) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ^n ↦ fieldDensity L (U p.1) p.2) (t, x) := by
  unfold fieldDensity
  exact (hL.of_le (by norm_num)).comp (t, x)
    ((contDiffAt_family_jacobianMatrix hU).prodMk
      ((hU.of_le (by norm_num)).prodMk contDiffAt_snd))

/-- Differentiating the density at fixed spatial coordinates gives its first variation.
The variation of the gradient is derived from local joint `C²` regularity. -/
theorem hasDerivAt_fieldDensity {t : ℝ}
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U t) x, (U t x, x)))
    (hU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (t, x)) :
    HasDerivAt (fun s ↦ fieldDensity L (U s) x)
      (firstVariationDensity L (U t) (fun y ↦ deriv (fun s ↦ U s y) t) x) t := by
  have hslice : ContDiffAt ℝ 2 (fun s : ℝ ↦ U s x) t :=
    hU.comp t (contDiffAt_id.prodMk contDiffAt_const)
  exact (hL.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_jacobianMatrix hU).prodMk
      ((hslice.differentiableAt (by norm_num)).hasDerivAt.prodMk
        (hasDerivAt_const t x)))

/-- The derivative of the pulled-back density consists of the field variation, transport
of the original density, and change in volume. All three terms come from chain rules. -/
theorem hasDerivAt_transformedDensity
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U 0) x, (U 0 x, x)))
    (hU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (0, x))
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id) :
    HasDerivAt (fun t ↦ transformedDensity L U Φ t x)
      (firstVariationDensity L (U 0) (fun y ↦ deriv (fun t ↦ U t y) 0) x +
        fderiv ℝ (fieldDensity L (U 0)) x (deriv (fun t ↦ Φ t x) 0) +
        fieldDensity L (U 0) x * ∇· (fun y ↦ deriv (fun t ↦ Φ t y) 0) x) 0 := by
  have hΦx : ContDiffAt ℝ 2 (fun t : ℝ ↦ Φ t x) 0 :=
    hΦ.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hbase : Φ 0 x = x := hΦ₀.eq_of_nhds
  have hmove := hasDerivAt_moving_point (U := fun t y ↦ fieldDensity L (U t) y)
    ((contDiffAt_family_fieldDensity hL hU).differentiableAt (by norm_num))
    (hΦx.differentiableAt (by norm_num)).hasDerivAt hbase
  rw [(hasDerivAt_fieldDensity hL hU).deriv] at hmove
  have h := hmove.fun_mul (hasDerivAt_spatial_volume hΦ hΦ₀)
  have hidentity : jacobianMatrix (Φ 0) x = 1 := by
    rw [jacobianMatrix_eq_of_eventuallyEq hΦ₀]
    exact jacobianMatrix_id x
  simpa only [transformedDensity, hidentity, Matrix.det_one, mul_one,
    hbase] using h

/-- Noether's invariant-variation theorem for simultaneous field and space variations.
Local `C²` regularity, invariance of the transformed density and the classical Euler–Lagrange
equations imply conservation of the current. Neither the infinitesimal invariance
identity nor the current's divergence is an assumption. -/
theorem noether_of_invariant_variation
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U 0) x, (U 0 x, x)))
    (hU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (0, x))
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id)
    (hinvariant : (fun t ↦ transformedDensity L U Φ t x) =ᶠ[𝓝 0]
      (fun _ ↦ fieldDensity L (U 0) x))
    (hEL : ∀ k, classicalEulerLagrange L (U 0) x k = 0) :
    ∇· (noetherCurrent L (U 0)
      (fun y ↦ deriv (fun t ↦ U t y) 0)
      (fun y ↦ deriv (fun t ↦ Φ t y) 0)) x = 0 := by
  have hu : ContDiffAt ℝ 2 (U 0) x :=
    hU.comp x (contDiffAt_const.prodMk contDiffAt_id)
  rw [divergence_noetherCurrent hL hu
    ((contDiffAt_parameter_deriv hU).differentiableAt (by norm_num))
    ((contDiffAt_parameter_deriv hΦ).differentiableAt (by norm_num))]
  simp only [hEL, zero_mul, Finset.sum_const_zero, sub_zero]
  exact (hasDerivAt_transformedDensity hL hU hΦ hΦ₀).unique
    ((hasDerivAt_const 0 (fieldDensity L (U 0) x)).congr_of_eventuallyEq
      hinvariant)

end PDE.CalculusOfVariations.Noether
