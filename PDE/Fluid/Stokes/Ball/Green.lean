/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Analysis.Calculus.EuclideanBall.NormalCutoff
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Green identity for the Neumann-type Stokes eigenproblem on a ball

Let `B` be the ball of radius `R` about the origin in `ℝ³`. Suppose a smooth field `ψ` and a
smooth pressure `p` satisfy `Δψ - ∇p = -μ ψ` in `B` and `(∇ψ) x = p x` on the sphere
`‖x‖ = R`, that is, the pseudo-traction `(∇ψ - p I) n` of the Laplacian form of the Stokes
operator vanishes there. This is the natural boundary condition of the Rayleigh quotient
`‖∇u‖² / ‖u‖²` over divergence-free fields with no boundary condition (Hou, Wang and Yang,
Appendix E). For every weakly divergence-free field `v` with `v, ∇v ∈ L¹(B)`,

`∫_B ∇ψ : ∇v = μ ∫_B ⟪ψ, v⟫`.

The proof applies `PDE.Analysis.integral_sum_mul_partialDeriv_add_mul_eq_zero` to the matrix
field `T = ∇ψ - p I`, whose rows have divergence `-μ ψᵢ` and whose normal component `T x`
vanishes on the sphere; the divergence condition removes the pressure term.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 6.2, (6.2), p. 50, and
  Appendix E, Step 1 of the proof of Lemma 4 and (E.1), p. 63.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory
open PDE (partialDeriv laplacian)
open Filter Metric Set
open scoped ContDiff RealInnerProductSpace

namespace PDE.Fluid.Stokes.Ball

/-- Green identity for the Neumann-type Stokes eigenproblem on the ball of radius `R` in `ℝ³`
(Hou, Wang and Yang, Appendix E). If `Δψ - ∇p = -μ ψ` in the ball and the pseudo-traction
`(∇ψ - p I) n` vanishes on the sphere, `(∇ψ) x = p x` for `‖x‖ = R`, then every divergence-free
field `v` with integrable weak derivatives `Dv i j = ∂ⱼ vᵢ` satisfies `∫ ∇ψ : ∇v = μ ∫ ⟪ψ, v⟫`.
-/
theorem integral_gradient_pairing_eq_of_neumann {R μ : ℝ} (hR : 0 < R)
    {ψ : ℝ^3 → ℝ^3} {p : ℝ^3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hp : ContDiff ℝ ∞ p)
    (heq : ∀ x ∈ Metric.ball (0 : ℝ^3) R, ∀ i : Fin 3,
      laplacian (fun y ↦ ψ y i) x - ∂[i] p x = -(μ * ψ x i))
    (hbc : ∀ x : ℝ^3, ‖x‖ = R → ∀ i : Fin 3,
      ∑ j : Fin 3, ∂[j] (fun y ↦ ψ y i) x * x j = p x * x i)
    {v : ℝ^3 → ℝ^3} {Dv : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hv : ∀ i, IntegrableOn (fun x ↦ v x i) (Metric.ball (0 : ℝ^3) R))
    (hDv : ∀ i j, IntegrableOn (Dv i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ v x i) (Dv i j))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)), ∑ i, Dv i i x = 0) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j, ∂[j] (fun y ↦ ψ y i) x * Dv i j x =
      μ * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪ψ x, v x⟫ := by
  simp only [EuclideanSpace.real_inner_eq_sum]
  set B := ball (0 : ℝ^3) R
  have hψi : ∀ i, ContDiff ℝ ∞ (fun y ↦ ψ y i) := fun i ↦ (contDiff_piLp_apply 2).comp hψ
  -- The matrix field `T = ∇ψ - p I` of the Laplacian form.
  set T : Fin 3 → Fin 3 → ℝ^3 → ℝ := fun i j y ↦
    ∂[j] (fun z ↦ ψ z i) y - (if i = j then 1 else 0) * p y with hT_def
  have hTdef : ∀ i j y,
      T i j y = ∂[j] (fun z ↦ ψ z i) y - (if i = j then 1 else 0) * p y := fun _ _ _ ↦ rfl
  have hTeq : ∀ i j,
      T i j = fun y ↦ ∂[j] (fun z ↦ ψ z i) y - (if i = j then 1 else 0) * p y := fun _ _ ↦ rfl
  have hT : ∀ i j, ContDiff ℝ ∞ (T i j) := fun i j ↦ by
    rw [hTeq]
    exact ((hψi i).partialDeriv j).sub (contDiff_const.mul hp)
  have hdT : ∀ i j x, ∂[j] (T i j) x =
      ∂[j] (fun y ↦ ∂[j] (fun z ↦ ψ z i) y) x - (if i = j then 1 else 0) * ∂[j] p x := by
    intro i j x
    have h₁ : DifferentiableAt ℝ (∂[j] (fun z ↦ ψ z i)) x :=
      ((hψi i).partialDeriv j).differentiable (by simp) x
    have h₂ : DifferentiableAt ℝ (fun y ↦ (if i = j then (1 : ℝ) else 0) * p y) x :=
      (contDiff_const.mul hp).differentiable (by simp) x
    rw [hTeq, partialDeriv_sub h₁ h₂, partialDeriv_mul (differentiableAt_const _)
      (hp.differentiable (by simp) x), partialDeriv_const, zero_mul, zero_add]
  -- The momentum equation and the boundary condition in terms of `T`.
  have hdivT : ∀ x ∈ B, ∀ i, ∑ j, ∂[j] (T i j) x = -(μ * ψ x i) := by
    intro x hx i
    simp only [hdT, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    exact heq x hx i
  have hTn : ∀ x : ℝ^3, ‖x‖ = R → ∀ i, ∑ j, T i j x * x j = 0 := by
    intro x hx i
    simp only [hTdef, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [hbc x hx i, sub_self]
  have hG := PDE.Analysis.integral_sum_mul_partialDeriv_add_mul_eq_zero hR hT hTn
    (v := fun i x ↦ v x i) hv hDv hweak
  -- Integrability of the two sides.
  have hmul : ∀ {g : ℝ^3 → ℝ}, Continuous g → ∀ {f : ℝ^3 → ℝ}, IntegrableOn f B →
      Integrable (fun x ↦ f x * g x) (volume.restrict B) := fun hg _ hf ↦
    hf.mul_continuousOn_of_subset hg.continuousOn measurableSet_ball
      (isCompact_closedBall 0 R) ball_subset_closedBall
  have hI₁ : Integrable (fun x ↦ ∑ i, ∑ j, (v x i * ∂[j] (T i j) x + Dv i j x * T i j x))
      (volume.restrict B) :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      (hmul (contDiff_top_partialDeriv (i := j) (hT i j)).continuous (hv i)).add
        (hmul (hT i j).continuous (hDv i j))
  have hI₂ : Integrable (fun x ↦ ∑ i, ψ x i * v x i) (volume.restrict B) :=
    integrable_finsetSum _ fun i _ ↦ IntegrableOn.continuousOn_mul_of_subset
      (hψi i).continuous.continuousOn (hv i) (isCompact_closedBall 0 R) measurableSet_ball
      ball_subset_closedBall
  -- Pointwise algebra, using the divergence condition.
  have hae : ∀ᵐ x ∂(volume.restrict B), ∑ i, ∑ j, ∂[j] (fun y ↦ ψ y i) x * Dv i j x =
      ∑ i, ∑ j, (v x i * ∂[j] (T i j) x + Dv i j x * T i j x) +
        μ * ∑ i, ψ x i * v x i := by
    filter_upwards [hdiv, ae_restrict_mem measurableSet_ball] with x hx0 hxB
    have h₀ := hdivT x hxB 0
    have h₁ := hdivT x hxB 1
    have h₂ := hdivT x hxB 2
    simp only [Fin.sum_univ_three, hTdef] at h₀ h₁ h₂ hx0 ⊢
    simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, one_mul, zero_mul, sub_zero]
    linear_combination (-v x 0) * h₀ - v x 1 * h₁ - v x 2 * h₂ + p x * hx0
  rw [integral_congr_ae hae, integral_add hI₁ (hI₂.const_mul μ), hG, integral_const_mul,
    zero_add]

end PDE.Fluid.Stokes.Ball
