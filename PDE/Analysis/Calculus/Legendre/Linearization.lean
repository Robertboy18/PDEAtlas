/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.InverseFunction.Coordinates
public import PDE.Analysis.Calculus.Legendre.Local
import CAS.ExactTactic

/-!
# Planar PDEs under local Legendre duality

In two dimensions, multiplying the dual Hessian by the original signed determinant gives
the original Hessian's adjugate. A quasilinear equation whose coefficients depend on the
gradient therefore becomes a linear equation in the dual potential, with coefficients
depending on the new independent variable. This is the Legendre transform of Evans,
§4.4.3(b), which he applies to the minimal surface equation.

Evans inverts `p = Du(x)` by the inverse function theorem where `J = det D²u ≠ 0`, defines the
dual `v` by (28) and derives (29) by calculation. We take the local inverse and the dual from
`exists_localLegendre_inverse_hessian`. The gradient of the dual is the local inverse of `∇u`,
so its Hessian is the inverse of the Hessian of `u`, which in two dimensions is the adjugate
divided by the determinant.

## Main results

* `inverse_gradient_cofactors`: Evans's identities (29), in the form
  `det (D²u) • D²v = adjugate (D²u)`.
* `inverse_gradient_secondOrder_eq`: the resulting transformation of a planar second-order
  expression with scalar coefficients.
* `exists_localLegendre_linearized`: near a point where the Hessian determinant is nonzero, a
  `C²` solution of a planar equation whose coefficients depend on the gradient has a local
  `C²` Legendre dual solving the corresponding linear equation. For the minimal surface
  equation (24) this is Evans's (30).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.3(b), (24)-(30), p. 210.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Filter Topology
open scoped Gradient

namespace PDE.Analysis

/-- The coordinate Jacobian of a gradient is the matrix of second partial derivatives.
The row is the inner derivative and the column is the outer derivative. -/
theorem jacobianMatrix_gradient_apply {n : ℕ} (u : ℝ^n → ℝ) (x : ℝ^n)
    (i j : Fin n) :
    jacobianMatrix (∇ u) x i j = (∂[j] (∂[i] u)) x := by
  simp only [jacobianMatrix, jacobianColumn, Matrix.of_apply, gradient_apply_eq_partialDeriv]

/-- The coordinate Hessians of a potential and its local dual obey the signed cofactor
identity. The gradient of the dual is prescribed only on the inverse chart's open target. -/
theorem inverse_gradient_cofactors
    {u v : ℝ^2 → ℝ} (e : OpenPartialHomeomorph (ℝ^2) (ℝ^2))
    (he : (e : ℝ^2 → ℝ^2) = ∇ u) {p : ℝ^2} (hp : p ∈ e.target)
    (hu : DifferentiableAt ℝ (∇ u) (e.symm p))
    (hi : DifferentiableAt ℝ e.symm p)
    (hv : ∀ q ∈ e.target, HasGradientAt v (e.symm q) q) :
    (jacobianMatrix (∇ u) (e.symm p)).det • jacobianMatrix (∇ v) p =
      !![(jacobianMatrix (∇ u) (e.symm p)) 1 1,
          -(jacobianMatrix (∇ u) (e.symm p)) 0 1;
        -(jacobianMatrix (∇ u) (e.symm p)) 1 0,
          (jacobianMatrix (∇ u) (e.symm p)) 0 0] := by
  have hJ : jacobianMatrix (∇ v) p = jacobianMatrix e.symm p := by
    ext i j
    apply partialDeriv_congr_nhds j
    filter_upwards [e.open_target.mem_nhds hp] with q hq
    exact congrArg (fun w : ℝ^2 ↦ w i) (hv q hq).gradient
  rw [hJ]
  simpa only [he] using inverse_chart_jacobian_cofactors e hp (he.symm ▸ hu) hi

/-- A planar second-order expression transforms by the signed original Hessian determinant.
The coefficients here are arbitrary scalars evaluated at the momentum point. -/
theorem inverse_gradient_secondOrder_eq
    {u v : ℝ^2 → ℝ} (e : OpenPartialHomeomorph (ℝ^2) (ℝ^2))
    (he : (e : ℝ^2 → ℝ^2) = ∇ u) {p : ℝ^2} (hp : p ∈ e.target)
    (hu : DifferentiableAt ℝ (∇ u) (e.symm p))
    (hi : DifferentiableAt ℝ e.symm p)
    (hv : ∀ q ∈ e.target, HasGradientAt v (e.symm q) q) (a b c : ℝ) :
    a * (∂[0] (∂[0] u)) (e.symm p) +
        2 * b * (∂[0] (∂[1] u)) (e.symm p) +
        c * (∂[1] (∂[1] u)) (e.symm p) =
      (jacobianMatrix (∇ u) (e.symm p)).det *
        (c * (∂[0] (∂[0] v)) p - 2 * b * (∂[0] (∂[1] v)) p +
          a * (∂[1] (∂[1] v)) p) := by
  have hcof := inverse_gradient_cofactors e he hp hu hi hv
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 0 0) hcof
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 1 0) hcof
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 1 1) hcof
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one,
    jacobianMatrix_gradient_apply] at h00 h10 h11
  cas using [h00, h10, h11]

/-- A nondegenerate C² solution of a gradient-dependent planar equation has a local C²
Legendre dual solving the corresponding linear PDE. The local inverse is a conclusion,
and neither convexity nor a prescribed inverse is assumed. -/
theorem exists_localLegendre_linearized
    {u : ℝ^2 → ℝ} {Ω : Set (ℝ^2)} {x : ℝ^2}
    (hΩ : IsOpen Ω) (hx : x ∈ Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (hdet : (jacobianMatrix (∇ u) x).det ≠ 0)
    (a b c : ℝ^2 → ℝ)
    (hPDE : ∀ y ∈ Ω,
      a (∇ u y) * (∂[0] (∂[0] u)) y +
        2 * b (∇ u y) * (∂[0] (∂[1] u)) y +
        c (∇ u y) * (∂[1] (∂[1] u)) y = 0) :
    ∃ e : OpenPartialHomeomorph (ℝ^2) (ℝ^2),
      (e : ℝ^2 → ℝ^2) = ∇ u ∧ x ∈ e.source ∧ e.source ⊆ Ω ∧
        ContDiffOn ℝ 1 e.symm e.target ∧
          ContDiffOn ℝ 2 (localLegendre u e.symm) e.target ∧
            (∀ p ∈ e.target, HasGradientAt (localLegendre u e.symm) (e.symm p) p) ∧
              ∀ p ∈ e.target,
                c p * (∂[0] (∂[0] (localLegendre u e.symm))) p -
                    2 * b p * (∂[0] (∂[1] (localLegendre u e.symm))) p +
                    a p * (∂[1] (∂[1] (localLegendre u e.symm))) p = 0 := by
  obtain ⟨e, he, hxe, hsource, hi, hv, hgrad, _hHessian⟩ :=
    exists_localLegendre_inverse_hessian hΩ hx hu hdet
  refine ⟨e, he, hxe, hsource, hi, hv, hgrad, ?_⟩
  intro p hp
  have hg := (contDiffAt_gradient (m := 1)
    (hu.contDiffAt (hΩ.mem_nhds (hsource (e.map_target hp))))).differentiableAt one_ne_zero
  have hXi := (hi.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt one_ne_zero
  have hd : (jacobianMatrix (∇ u) (e.symm p)).det ≠ 0 := by
    have h := left_ne_zero_of_mul_eq_one
      (inverse_chart_det_mul e hp (he.symm ▸ hg) hXi)
    simpa only [he] using h
  have hvalue : ∇ u (e.symm p) = p := he ▸ e.right_inv hp
  have hzero := hPDE (e.symm p) (hsource (e.map_target hp))
  rw [hvalue, inverse_gradient_secondOrder_eq e he hp hg hXi hgrad] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left hd

end PDE.Analysis
