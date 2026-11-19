/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.InverseFunction.Coordinates
public import PDE.Analysis.Calculus.Potential.Convex
import CAS.ExactTactic

/-!
# Local hodograph reduction of planar potential flow

For the steady planar irrotational flow system (17) of Evans (§4.4.3(a)), velocity becomes the
independent variable. A nonzero velocity Jacobian at one point gives a local C¹ inverse, and the
inverse satisfies transformed equations (`linearMassResidual`, `curlResidual`) that are linear in
it (`exists_inverse_solution`). On a ball inside its target, the curl equation
produces a C² scalar potential `z` with `linearPotentialResidual σ z = 0`
(`exists_hodograph_potential`).

The sound-speed coefficient is an arbitrary function of velocity; no sign or regularity
of it is needed for this substitution. The inverse and the potential are local. The algebra
relating the residuals of the flow to those of its inverse is done by the `cas` tactic of SymLean,
our computer algebra system for Lean.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.3(a), equations (17)-(23) and the Remark that follows
  them, p. 209.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Filter Topology
open scoped Gradient

namespace PDE.Fluid.Hodograph

open PDE.Analysis

/-- The planar compressible mass equation, with sound speed evaluated at velocity. -/
def massResidual (σ : ℝ^2 → ℝ) (u : ℝ^2 → ℝ^2) (x : ℝ^2) : ℝ :=
  (σ (u x) ^ 2 - (u x 0) ^ 2) * jacobianMatrix u x 0 0 -
    u x 0 * u x 1 * (jacobianMatrix u x 0 1 + jacobianMatrix u x 1 0) +
    (σ (u x) ^ 2 - (u x 1) ^ 2) * jacobianMatrix u x 1 1

/-- The off-diagonal derivative difference `∂₂u¹ - ∂₁u²`. -/
def curlResidual (u : ℝ^2 → ℝ^2) (x : ℝ^2) : ℝ :=
  jacobianMatrix u x 0 1 - jacobianMatrix u x 1 0

/-- The mass equation after velocity becomes the independent variable.
This expression is linear in the derivatives of the inverse map X. -/
def linearMassResidual (σ : ℝ^2 → ℝ) (X : ℝ^2 → ℝ^2) (q : ℝ^2) : ℝ :=
  (σ q ^ 2 - (q 0) ^ 2) * jacobianMatrix X q 1 1 +
    q 0 * q 1 * (jacobianMatrix X q 0 1 + jacobianMatrix X q 1 0) +
    (σ q ^ 2 - (q 1) ^ 2) * jacobianMatrix X q 0 0

/-- The scalar linear PDE for a potential of the inverse velocity map. -/
def linearPotentialResidual (σ : ℝ^2 → ℝ) (z : ℝ^2 → ℝ) (q : ℝ^2) : ℝ :=
  (σ q ^ 2 - (q 0) ^ 2) * (∂[1] (∂[1] z)) q +
    2 * q 0 * q 1 * (∂[0] (∂[1] z)) q +
    (σ q ^ 2 - (q 1) ^ 2) * (∂[0] (∂[0] z)) q

/-- The original mass residual is the transformed residual times the signed Jacobian.
Both orientations of a local inverse are allowed. -/
theorem massResidual_inverse_eq (σ : ℝ^2 → ℝ)
    (e : OpenPartialHomeomorph (ℝ^2) (ℝ^2)) {q : ℝ^2} (hq : q ∈ e.target)
    (he : DifferentiableAt ℝ e (e.symm q)) (hi : DifferentiableAt ℝ e.symm q) :
    massResidual σ e (e.symm q) =
      (jacobianMatrix e (e.symm q)).det * linearMassResidual σ e.symm q := by
  have hcof := inverse_chart_jacobian_cofactors e hq he hi
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 0 0) hcof
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 0 1) hcof
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 1 0) hcof
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 1 1) hcof
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
    at h00 h01 h10 h11
  unfold massResidual linearMassResidual
  rw [e.right_inv hq]
  cas using [h00, h01, h10, h11]

/-- The curl equation is preserved by inversion, with a minus sign and the signed determinant. -/
theorem curlResidual_inverse_eq
    (e : OpenPartialHomeomorph (ℝ^2) (ℝ^2)) {q : ℝ^2} (hq : q ∈ e.target)
    (he : DifferentiableAt ℝ e (e.symm q)) (hi : DifferentiableAt ℝ e.symm q) :
    curlResidual e (e.symm q) =
      -(jacobianMatrix e (e.symm q)).det * curlResidual e.symm q := by
  have hcof := inverse_chart_jacobian_cofactors e hq he hi
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 0 1) hcof
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 1 0) hcof
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
    at h01 h10
  unfold curlResidual
  cas using [h01, h10]

/-- For a C² scalar potential, the transformed mass equation is the scalar linear equation. -/
theorem linearMassResidual_gradient (σ : ℝ^2 → ℝ) {z : ℝ^2 → ℝ} {q : ℝ^2}
    (hz : ContDiffAt ℝ 2 z q) :
    linearMassResidual σ (∇ z) q = linearPotentialResidual σ z q := by
  unfold linearMassResidual linearPotentialResidual
  simp only [jacobianMatrix, jacobianColumn, Matrix.of_apply, gradient_apply_eq_partialDeriv]
  rw [partialDeriv_partialDeriv_comm_at 1 0 hz]
  cas

/-- A C¹ solution of the original system with nonzero Jacobian at one point has a local
inverse satisfying both transformed linear equations throughout its open target. -/
theorem exists_inverse_solution
    {u : ℝ^2 → ℝ^2} {Ω : Set (ℝ^2)} {x : ℝ^2}
    (hΩ : IsOpen Ω) (hx : x ∈ Ω) (hu : ContDiffOn ℝ 1 u Ω)
    (hdet : (jacobianMatrix u x).det ≠ 0) (σ : ℝ^2 → ℝ)
    (hmass : ∀ y ∈ Ω, massResidual σ u y = 0)
    (hcurl : ∀ y ∈ Ω, curlResidual u y = 0) :
    ∃ e : OpenPartialHomeomorph (ℝ^2) (ℝ^2),
      (e : ℝ^2 → ℝ^2) = u ∧ x ∈ e.source ∧ e.source ⊆ Ω ∧
        ContDiffOn ℝ 1 e.symm e.target ∧
          ∀ q ∈ e.target, linearMassResidual σ e.symm q = 0 ∧
            curlResidual e.symm q = 0 := by
  obtain ⟨e, he, hxe, hsource, hi, hregular⟩ :=
    exists_regular_contDiffOn_inverse_chart hΩ hx hu hdet
  refine ⟨e, he, hxe, hsource, hi, ?_⟩
  intro q hq
  have hsourceq := hsource (e.map_target hq)
  have hd : DifferentiableAt ℝ e (e.symm q) := by
    rw [he]
    exact (hu.contDiffAt (hΩ.mem_nhds hsourceq)).differentiableAt one_ne_zero
  have hdi := (hi.contDiffAt (e.open_target.mem_nhds hq)).differentiableAt one_ne_zero
  have hn : (jacobianMatrix e (e.symm q)).det ≠ 0 := by
    rw [he]
    exact hregular _ (e.map_target hq)
  have hm : massResidual σ e (e.symm q) = 0 := he.symm ▸ hmass _ hsourceq
  have hc : curlResidual e (e.symm q) = 0 := he.symm ▸ hcurl _ hsourceq
  rw [massResidual_inverse_eq σ e hq hd hdi] at hm
  rw [curlResidual_inverse_eq e hq hd hdi] at hc
  exact ⟨(mul_eq_zero.mp hm).resolve_left hn,
    (mul_eq_zero.mp hc).resolve_left (neg_ne_zero.mpr hn)⟩

/-- The local inverse velocity admits a C² potential on a ball in its target, and this
potential solves the scalar linear hodograph PDE. Only the original nonlinear mass
and curl equations are hypotheses; local inversion and potential construction are conclusions. -/
theorem exists_hodograph_potential
    {u : ℝ^2 → ℝ^2} {Ω : Set (ℝ^2)} {x : ℝ^2}
    (hΩ : IsOpen Ω) (hx : x ∈ Ω) (hu : ContDiffOn ℝ 1 u Ω)
    (hdet : (jacobianMatrix u x).det ≠ 0) (σ : ℝ^2 → ℝ)
    (hmass : ∀ y ∈ Ω, massResidual σ u y = 0)
    (hcurl : ∀ y ∈ Ω, curlResidual u y = 0) :
    ∃ (e : OpenPartialHomeomorph (ℝ^2) (ℝ^2)) (r : ℝ) (z : ℝ^2 → ℝ),
      (e : ℝ^2 → ℝ^2) = u ∧ x ∈ e.source ∧ e.source ⊆ Ω ∧
        ContDiffOn ℝ 1 e.symm e.target ∧ 0 < r ∧
          Metric.ball (u x) r ⊆ e.target ∧
            ContDiffOn ℝ 2 z (Metric.ball (u x) r) ∧
              (∀ q ∈ Metric.ball (u x) r, HasGradientAt z (e.symm q) q) ∧
                ∀ q ∈ Metric.ball (u x) r, linearPotentialResidual σ z q = 0 := by
  obtain ⟨e, he, hxe, hsource, hi, hPDE⟩ :=
    exists_inverse_solution hΩ hx hu hdet σ hmass hcurl
  have hcenter : u x ∈ e.target := he ▸ e.map_source hxe
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hcenter)
  have hX : ContDiffOn ℝ 1 e.symm (Metric.ball (u x) r) := hi.mono hball
  have hcomm (q : ℝ^2) (hq : q ∈ Metric.ball (u x) r) (i j : Fin 2) :
      (∂[i] (fun y ↦ e.symm y j)) q = (∂[j] (fun y ↦ e.symm y i)) q := by
    have hc := sub_eq_zero.mp (hPDE q (hball hq)).2
    change jacobianMatrix e.symm q 0 1 = jacobianMatrix e.symm q 1 0 at hc
    fin_cases i <;> fin_cases j
    · rfl
    · exact hc.symm
    · exact hc
    · rfl
  obtain ⟨z, hz, hgrad⟩ :=
    InnerProductSpace.exists_contDiffOn_potential_of_fderiv_symmetric
      (convex_ball (u x) r) Metric.isOpen_ball (k := 1) one_ne_zero hX
      (fun q hq ↦ EuclideanSpace.inner_fderiv_apply_comm_of_partialDeriv_comm
        e.symm q ((hX.contDiffAt (Metric.isOpen_ball.mem_nhds hq)).differentiableAt
          one_ne_zero) (hcomm q hq))
  refine ⟨e, r, z, he, hxe, hsource, hi, hr, hball, hz, hgrad, ?_⟩
  intro q hq
  have hJ : jacobianMatrix (∇ z) q = jacobianMatrix e.symm q := by
    ext i j
    apply partialDeriv_congr_nhds j
    filter_upwards [Metric.isOpen_ball.mem_nhds hq] with p hp
    exact congrArg (fun w : ℝ^2 ↦ w i) (hgrad p hp).gradient
  rw [← linearMassResidual_gradient σ (hz.contDiffAt (Metric.isOpen_ball.mem_nhds hq))]
  unfold linearMassResidual
  rw [hJ]
  exact (hPDE q (hball hq)).1

end PDE.Fluid.Hodograph
