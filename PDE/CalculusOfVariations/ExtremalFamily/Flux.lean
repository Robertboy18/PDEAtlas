/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.Noether.Invariance
public import PDE.CalculusOfVariations.SlopeField.Basic
public import PDE.Analysis.Convex.Differentiable.Supporting
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Fluxes of extremal families

The momentum paired with the parameter velocity is the flux of a one-parameter
family. Along Euler–Lagrange solutions its divergence is the parameter derivative
of the Lagrangian density. The density of the graph selected by a spatially varying
parameter is the density of the family member through the point, plus the pairing of the flux
with the differential of the parameter, plus Weierstrass's excess `graphExcess`; convexity in
the matrix variable makes the excess nonnegative. The excess is
`SlopeField.weierstrassExcess` of the density as a function of the matrix variable
(`graphExcess_eq_weierstrassExcess`), and its sign comes from
`SlopeField.weierstrassExcess_nonneg_of_convexOn`. This is the
pointwise part of the proof of Evans, §8.2.5, Theorem 10 (the convexity bound (61) and the
divergence of the vector field (62)), with arbitrary finite target dimension.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.5, proof of Theorem 10.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set
open scoped Matrix.Norms.Elementwise Topology

namespace PDE.CalculusOfVariations.ExtremalFamily

open Analysis Noether

variable {n m : ℕ}

/-- Momentum paired with the velocity of a family at a fixed spatial point. -/
def familyFlux (L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ)
    (U : ℝ → ℝ^n → ℝ^m) (t : ℝ) (x : ℝ^n) : ℝ^n :=
  noetherCurrent L (U t) (fun y ↦ deriv (fun s ↦ U s y) t) (fun _ ↦ 0) x

variable {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
  {U : ℝ → ℝ^n → ℝ^m} {t : ℝ} {x : ℝ^n}

/-- The family flux is jointly `C¹` wherever the family and density are `C²`. -/
theorem contDiffAt_familyFlux
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U t) x, (U t x, x)))
    (hU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (t, x)) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ^n ↦ familyFlux L U p.1 p.2) (t, x) := by
  have hjet := (contDiffAt_family_jacobianMatrix hU).prodMk
    ((hU.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)).prodMk contDiffAt_snd)
  have hv : ContDiffAt ℝ 1 (fun p : ℝ × ℝ^n ↦ deriv (fun s ↦ U s p.2) p.1)
      (t, x) := by
    apply ContDiffAt.congr_of_eventuallyEq
      ((hU.fderiv_right (m := 1) (by norm_num)).clm_apply
        (contDiffAt_const (c := ((1 : ℝ), (0 : ℝ^n)))))
    filter_upwards [hU.eventually (by norm_num)] with p hp
    exact deriv_parameter_eq (hp.differentiableAt (by norm_num))
  apply contDiffAt_euclidean.mpr
  intro i
  have hm (k : Fin m) : ContDiffAt ℝ 1
      (fun p : ℝ × ℝ^n ↦ momentum L (U p.1) k i p.2) (t, x) := by
    apply ContDiffAt.congr_of_eventuallyEq
      (((hL.fderiv_right (m := 1) (by norm_num)).comp (t, x) hjet).clm_apply
        (contDiffAt_const (c := (Matrix.single k i 1, (0, 0)))))
    filter_upwards [hjet.continuousAt.eventually (hL.eventually (by norm_num))] with p hp
    exact fderiv_lagrangian_matrix_apply (hp.differentiableAt (by norm_num)) _
  simpa [familyFlux, noetherCurrent, Function.comp_def] using
    ContDiffAt.sum (fun k _ ↦ (hm k).mul
      ((EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).contDiff.contDiffAt.comp (t, x) hv))

/-- The Euler–Lagrange equations turn the divergence of the family flux into
the parameter derivative of the density. -/
theorem hasDerivAt_fieldDensity_divergence_familyFlux
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U t) x, (U t x, x)))
    (hU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (t, x))
    (hEL : ∀ k, classicalEulerLagrange L (U t) x k = 0) :
    HasDerivAt (fun s ↦ fieldDensity L (U s) x) (∇· (familyFlux L U t) x) t := by
  have hu : ContDiffAt ℝ 2 (U t) x :=
    hU.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hv := (contDiffAt_parameter_deriv hU).differentiableAt (by norm_num)
  have hdiv := divergence_noetherCurrent hL hu hv
    (differentiableAt_const (0 : ℝ^n))
  have hzero : ∇· (fun _ : ℝ^n ↦ (0 : ℝ^n)) x = 0 := by
    simp [divergence, partialDeriv_const]
  simp only [hEL, zero_mul, Finset.sum_const_zero, sub_zero, map_zero,
    add_zero, hzero, mul_zero] at hdiv
  change HasDerivAt _ (∇· (noetherCurrent L (U t)
    (fun y ↦ deriv (fun s ↦ U s y) t) (fun _ ↦ 0)) x) t
  rw [hdiv]
  exact hasDerivAt_fieldDensity hL hU

/-- The derivative of a graph chosen from a family includes the parameter-velocity
term. The identity is pointwise and imposes no sign on the velocity. -/
theorem jacobianMatrix_parameter_graph {θ : ℝ^n → ℝ}
    (hU : DifferentiableAt ℝ (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (θ x, x))
    (hθ : DifferentiableAt ℝ θ x) (k : Fin m) (i : Fin n) :
    jacobianMatrix (fun y ↦ U (θ y) y) x k i =
      jacobianMatrix (U (θ x)) x k i +
        deriv (fun s ↦ U s x) (θ x) k * (∂[i] θ) x := by
  have hd := hU.hasFDerivAt.comp (f := fun y : ℝ^n ↦ (θ y, y)) x
    (hθ.hasFDerivAt.prodMk (hasFDerivAt_id x))
  have hs := hU.comp (f := fun y : ℝ^n ↦ (θ x, y)) x
    ((differentiableAt_const (θ x)).prodMk differentiableAt_id)
  dsimp only [Function.comp_def] at hd hs
  erw [jacobianMatrix_apply_eq_fderiv hd.differentiableAt,
    jacobianMatrix_apply_eq_fderiv hs, hd.fderiv, fderiv_space_apply hU,
    deriv_parameter_eq hU]
  change (fderiv ℝ (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (θ x, x))
    ((∂[i] θ) x, EuclideanSpace.single i 1) k = _
  have hsplit : ((∂[i] θ) x, EuclideanSpace.single i (1 : ℝ)) =
      ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) +
        (∂[i] θ) x • ((1 : ℝ), (0 : ℝ^n)) := by simp
  rw [hsplit, map_add, map_smul]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_comm]

/-- The derivative of the density in the gradient, taken at the Jacobian of the member of the
family through the point and applied to the difference between the Jacobian of the parameter
graph and that Jacobian, is the endpoint pairing of the family flux. -/
theorem fderiv_gradient_parameter_graph_sub {θ : ℝ^n → ℝ}
    (hL : DifferentiableAt ℝ
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U (θ x)) x, (U (θ x) x, x)))
    (hU : DifferentiableAt ℝ (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (θ x, x))
    (hθ : DifferentiableAt ℝ θ x) :
    fderiv ℝ (fun P ↦ L P (U (θ x) x) x) (jacobianMatrix (U (θ x)) x)
      (jacobianMatrix (fun y ↦ U (θ y) y) x - jacobianMatrix (U (θ x)) x) =
      fderiv ℝ θ x (familyFlux L U (θ x) x) := by
  rw [fderiv_lagrangian_matrix_apply hL,
    fderiv_lagrangian_apply_matrix_value hL]
  simp only [PiLp.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    Matrix.sub_apply, jacobianMatrix_parameter_graph hU hθ, add_sub_cancel_left]
  rw [Finset.sum_comm, fderiv_apply_eq_sum_partialDeriv_mul]
  unfold familyFlux noetherCurrent momentum
  simp only [smul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.mul_sum, mul_assoc, mul_comm]

/-- Weierstrass's excess of a parameter graph over the field of a family, at the point `x`:
`E = L(Dw) - L(P) - ⟪L_P(P), Dw - P⟫`, where `w(y) = U (θ y) y` is the graph, `P` is the
Jacobian at `x` of the member `U (θ x)` of the family through the point `(x, w x)`, and the
density and its derivative in the gradient are taken at the value `w x`. -/
def graphExcess (L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ)
    (U : ℝ → ℝ^n → ℝ^m) (θ : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  fieldDensity L (fun y ↦ U (θ y) y) x - fieldDensity L (U (θ x)) x -
    fderiv ℝ (fun P ↦ L P (U (θ x) x) x) (jacobianMatrix (U (θ x)) x)
      (jacobianMatrix (fun y ↦ U (θ y) y) x - jacobianMatrix (U (θ x)) x)

/-- The excess of a parameter graph is the excess of the general theory of slope fields, for
the density as a function of the gradient: at the Jacobian of the graph, over the tangent
plane at the Jacobian of the member of the family through the point. -/
theorem graphExcess_eq_weierstrassExcess (L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ)
    (U : ℝ → ℝ^n → ℝ^m) (θ : ℝ^n → ℝ) (x : ℝ^n) :
    graphExcess L U θ x = SlopeField.weierstrassExcess (fun P ↦ L P (U (θ x) x) x)
      (jacobianMatrix (U (θ x)) x) (jacobianMatrix (fun y ↦ U (θ y) y) x) :=
  rfl

/-- The density of a parameter graph is the density of the member of the family through the
point, plus the endpoint pairing of the family flux, plus the excess. No convexity is used. -/
theorem fieldDensity_parameter_graph_eq {θ : ℝ^n → ℝ}
    (hL : DifferentiableAt ℝ
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U (θ x)) x, (U (θ x) x, x)))
    (hU : DifferentiableAt ℝ (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (θ x, x))
    (hθ : DifferentiableAt ℝ θ x) :
    fieldDensity L (fun y ↦ U (θ y) y) x =
      fieldDensity L (U (θ x)) x + fderiv ℝ θ x (familyFlux L U (θ x) x) +
        graphExcess L U θ x := by
  rw [graphExcess, fderiv_gradient_parameter_graph_sub hL hU hθ]
  ring

/-- The excess of a parameter graph is nonnegative when the density is convex in the gradient
at the value of the graph. This is `SlopeField.weierstrassExcess_nonneg_of_convexOn`. -/
theorem graphExcess_nonneg {θ : ℝ^n → ℝ}
    (hL : DifferentiableAt ℝ
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U (θ x)) x, (U (θ x) x, x)))
    (hconvex : ConvexOn ℝ univ (fun P ↦ L P (U (θ x) x) x)) :
    0 ≤ graphExcess L U θ x := by
  have hp := hL.hasFDerivAt.comp (jacobianMatrix (U (θ x)) x)
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) (jacobianMatrix (U (θ x)) x) (U (θ x) x, x))
  rw [graphExcess_eq_weierstrassExcess]
  exact SlopeField.weierstrassExcess_nonneg_of_convexOn hconvex hp.differentiableAt _

/-- Gradient convexity supplies a supporting density for a parameter graph.
Convexity in the value variable is not required. This is `fieldDensity_parameter_graph_eq`
with a nonnegative excess. -/
theorem fieldDensity_parameter_graph_ge {θ : ℝ^n → ℝ}
    (hL : DifferentiableAt ℝ
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U (θ x)) x, (U (θ x) x, x)))
    (hU : DifferentiableAt ℝ (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (θ x, x))
    (hθ : DifferentiableAt ℝ θ x)
    (hconvex : ConvexOn ℝ univ (fun P ↦ L P (U (θ x) x) x)) :
    fieldDensity L (U (θ x)) x + fderiv ℝ θ x (familyFlux L U (θ x) x) ≤
      fieldDensity L (fun y ↦ U (θ y) y) x := by
  have h1 := fieldDensity_parameter_graph_eq hL hU hθ
  have h2 := graphExcess_nonneg (θ := θ) hL hconvex
  linarith

end PDE.CalculusOfVariations.ExtremalFamily
