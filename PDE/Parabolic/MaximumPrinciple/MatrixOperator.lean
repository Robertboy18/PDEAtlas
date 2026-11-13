/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixOperator
public import PDE.Parabolic.MaximumPrinciple.WithPotential
import CAS.ExactTactic

/-!
# Parabolic operators with matrix coefficients

`matrixParabolicOperator a b c u` is `uₜ + Lu` for Evans's nondivergence form (61) in §7.1.4(a),
`Lu = -∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + Du · b + cu`, with the spatial part `EllipticMaximum.matrixOperator` frozen
at each time. At a point where `a` is positive semidefinite, Mathlib's factorization of positive
semidefinite matrices, through `EllipticMaximum.exists_factors_of_posSemidef`, writes
`aᵢⱼ = ∑ₖ (σₖ)ᵢ (σₖ)ⱼ`, and the matrix residual equals the factored one. The weak maximum principle
of Evans's Theorem 9 follows for positive semidefinite matrices and `c ≥ 0`. The factors are chosen
separately at each point, so neither continuity of `a` nor uniform parabolicity is needed.

## Main definitions

* `matrixParabolicOperator`: the operator `uₜ + Lu`.

## Main results

* `matrixParabolicOperator_eq_factored`: the matrix and factored residuals agree at a spatial `C²`
  point.
* `matrix_subsolution_le_of_boundary_le`: the weak maximum principle for positive semidefinite
  matrices and nonnegative potential.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.4(a), the nondivergence form (61), p. 389, and Theorem 9
  (Weak maximum principle for `c ≥ 0`), pp. 390-391.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace ParabolicMaximum

open Set

variable {n : ℕ}

/-- The parabolic operator `∂ₜu - ∑ aᵢⱼ ∂ᵢ∂ⱼu + Du · b + c u`: the time derivative
plus the matrix elliptic operator frozen at time `t`. -/
def matrixParabolicOperator
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    (u : ℝ^n → ℝ → ℝ) (x : ℝ^n) (t : ℝ) : ℝ :=
  deriv (u x) t +
    EllipticMaximum.matrixOperator (fun y ↦ a y t) (fun y ↦ b y t)
      (fun y ↦ c y t) (fun y ↦ u y t) x

/-- Matrix and factored parabolic residuals agree at a spatial `C²` point. -/
theorem matrixParabolicOperator_eq_factored
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (σ : ℝ^n → ℝ → Fin n → ℝ^n)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    {u : ℝ^n → ℝ → ℝ} {x : ℝ^n} {t : ℝ}
    (hu : ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hfactor : ∀ i j, a x t i j = ∑ k, σ x t k i * σ x t k j) :
    matrixParabolicOperator a b c u x t =
      factoredParabolicOperatorWithPotential σ b c u x t := by
  rw [matrixParabolicOperator,
    EllipticMaximum.matrixOperator_eq_factoredOperator
      (fun y ↦ a y t) (fun y ↦ σ y t) (fun y ↦ b y t) (fun y ↦ c y t) hu hfactor]
  simp only [factoredParabolicOperatorWithPotential, factoredParabolicOperator,
    factoredEllipticOperator, EllipticMaximum.factoredOperator]
  cas

/-- Only the potential acts on a spacetime constant. -/
theorem matrixParabolicOperator_const
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    (M : ℝ) (x : ℝ^n) (t : ℝ) :
    matrixParabolicOperator a b c (fun _ _ ↦ M) x t = c x t * M := by
  simp [matrixParabolicOperator, EllipticMaximum.matrixOperator_const]

/-- Multiplying the field by a constant `M` multiplies the residual by `M`. -/
theorem matrixParabolicOperator_const_mul
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    {u : ℝ^n → ℝ → ℝ} {x : ℝ^n} {t : ℝ}
    (hu : DifferentiableAt ℝ (fun y ↦ u y t) x)
    (hut : DifferentiableAt ℝ (u x) t) (M : ℝ) :
    matrixParabolicOperator a b c (fun y s ↦ M * u y s) x t =
      M * matrixParabolicOperator a b c u x t := by
  rw [matrixParabolicOperator, deriv_const_mul M hut,
    EllipticMaximum.matrixOperator_const_mul _ _ _ hu M, matrixParabolicOperator]
  cas

/-- Subtraction is linear when both spatial and time derivatives exist. -/
theorem matrixParabolicOperator_sub
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    {u v : ℝ^n → ℝ → ℝ} {x : ℝ^n} {t : ℝ}
    (hu : ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hv : ContDiffAt ℝ 2 (fun y ↦ v y t) x)
    (hut : DifferentiableAt ℝ (u x) t) (hvt : DifferentiableAt ℝ (v x) t) :
    matrixParabolicOperator a b c (fun y r ↦ u y r - v y r) x t =
      matrixParabolicOperator a b c u x t - matrixParabolicOperator a b c v x t := by
  simp only [matrixParabolicOperator, deriv_fun_sub hut hvt,
    EllipticMaximum.matrixOperator_sub _ _ _ hu hv]
  cas

/-- The weak maximum principle for positive semidefinite matrix coefficients, with no
regularity assumed on `a`. The factors needed by
`subsolution_with_potential_le_of_boundary_le` are chosen pointwise. -/
theorem matrix_subsolution_le_of_boundary_le
    {Ω : Set (ℝ^n)} {T M : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hT : 0 < T) (hM : 0 ≤ M)
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    (ha : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, (a x t).PosSemidef)
    (hc : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, 0 ≤ c x t)
    (u : ℝ^n → ℝ → ℝ)
    (hucont : ContinuousOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closedCylinder Ω T))
    (huspace : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, DifferentiableAt ℝ (u x) t)
    (hsub : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, matrixParabolicOperator a b c u x t ≤ 0)
    (hboundary : ∀ p ∈ parabolicBoundary Ω T, u p.1 p.2 ≤ M) :
    ∀ p ∈ closedCylinder Ω T, u p.1 p.2 ≤ M := by
  classical
  have hex : ∀ x t, ∃ σ : Fin n → ℝ^n,
      ∀ _ : x ∈ Ω, ∀ _ : t ∈ Ioc 0 T, ∀ i j,
        a x t i j = ∑ k, σ k i * σ k j := by
    intro x t
    by_cases hxt : x ∈ Ω ∧ t ∈ Ioc 0 T
    · obtain ⟨σ, hσ⟩ := EllipticMaximum.exists_factors_of_posSemidef (ha x hxt.1 t hxt.2)
      exact ⟨σ, fun _ _ ↦ hσ⟩
    · exact ⟨fun _ ↦ 0, fun hx ht ↦ False.elim (hxt ⟨hx, ht⟩)⟩
  choose σ hσ using hex
  apply subsolution_with_potential_le_of_boundary_le hΩopen hΩne hΩcompact hT hM
    σ b c hc u hucont huspace hutime ?_ hboundary
  intro x hx t ht
  rw [← matrixParabolicOperator_eq_factored a σ b c (huspace x hx t ht) (hσ x t hx ht)]
  exact hsub x hx t ht

end ParabolicMaximum
