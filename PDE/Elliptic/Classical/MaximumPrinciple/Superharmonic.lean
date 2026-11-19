/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixStrong

/-!
# Strict positivity of nonnegative superharmonic functions

On a connected open domain, a nonnegative classical supersolution of `−Δ + c`, for a real constant
`c`, that is positive somewhere is positive everywhere. Since `f ≥ 0`, `f` is also a supersolution
of `−Δ + max c 0`, and a zero of `f` would be a nonpositive interior minimum, which part (ii) of
Evans's §6.4.2, Theorem 4 excludes. The proof specializes the matrix strong maximum principle, with
local `C²` regularity and no boundedness or boundary condition. The zero-potential case gives strict
positivity of superharmonic functions.

## Main results

* `pos_of_nonneg_of_neg_laplacian_add_mul_nonneg`: the constant-potential case.
* `pos_of_nonneg_of_neg_laplacian_nonneg`: nonnegative superharmonic functions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.4.2, Theorem 4 (Strong maximum principle with `c ≥ 0`),
  pp. 350-351.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

noncomputable section

open Set Filter
open scoped Topology ENNReal InnerProductSpace

namespace EllipticMaximum

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A nonnegative supersolution of `−Δ + c` on a connected open domain is
strictly positive if it is positive at one point. No boundedness or boundary condition is
required, and the constant potential may have either sign: since `f ≥ 0`, `f` is also a
supersolution of `−Δ + max c 0`. -/
theorem pos_of_nonneg_of_neg_laplacian_add_mul_nonneg
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) {f : ℝ^n → ℝ}
    {c : ℝ}
    (hreg : ∀ x ∈ Ω, ContDiffAt ℝ 2 f x)
    (hnonneg : ∀ x ∈ Ω, 0 ≤ f x)
    (hsuper : ∀ x ∈ Ω, 0 ≤ -laplacian f x + c * f x)
    (hpositive : ∃ y ∈ Ω, 0 < f y) :
    ∀ x ∈ Ω, 0 < f x := by
  classical
  obtain ⟨c, hc, hsuper⟩ : ∃ c' : ℝ, 0 ≤ c' ∧ ∀ x ∈ Ω, 0 ≤ -laplacian f x + c' * f x :=
    ⟨max c 0, le_max_right _ _, fun x hx ↦ by
      nlinarith [hsuper x hx, hnonneg x hx, le_max_left c 0]⟩
  have hoperator (g : ℝ^n → ℝ) (x : ℝ^n) :
      matrixOperator (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℝ))
        (fun _ ↦ 0) (fun _ ↦ c) g x = -laplacian g x + c * g x := by
    simp [matrixOperator, laplacian, Matrix.one_apply]
  have hlocal (p : ℝ^n) (hp : p ∈ Ω) :
      ∃ r κ A B C : ℝ, 0 < r ∧ 0 < κ ∧ 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧
        Metric.closedBall p r ⊆ Ω ∧
        ∀ x ∈ Metric.ball p r,
          (∀ v : ℝ^n, κ * ‖v‖ ^ 2 ≤
            ∑ i : Fin n, ∑ j : Fin n, (1 : Matrix (Fin n) (Fin n) ℝ) i j * v i * v j) ∧
          (∑ i : Fin n, (1 : Matrix (Fin n) (Fin n) ℝ) i i) ≤ A ∧
          ‖(0 : ℝ^n)‖ ≤ B ∧ 0 ≤ c ∧ c ≤ C := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ p hp
    refine ⟨r / 2, 1, n, 0, c, half_pos hr, zero_lt_one,
      Nat.cast_nonneg n, le_rfl, hc,
      (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball, ?_⟩
    intro _ _
    refine ⟨?_, by simp, by simp, hc, le_rfl⟩
    intro v
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Matrix.one_apply, pow_two]
  intro x hx
  by_contra hnot
  have hzero : f x = 0 := le_antisymm (le_of_not_gt hnot) (hnonneg x hx)
  have hmax : IsMaxOn (fun y ↦ -f y) Ω x := by
    intro y hy
    change -f y ≤ -f x
    rw [hzero, neg_zero]
    exact neg_nonpos.mpr (hnonneg y hy)
  have hconstant := matrix_eqOn_const_of_isPreconnected_of_isMaxOn hΩ hconn
    (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℝ)) (fun _ ↦ 0) (fun _ ↦ c)
    (fun _ _ ↦ Matrix.isHermitian_one) hlocal
    (fun y hy ↦ (hreg y hy).neg) (fun y hy ↦ by
      rw [hoperator]
      change -laplacian (-f) y + c * -f y ≤ 0
      rw [PDE.laplacian_neg, neg_neg]
      linarith [hsuper y hy]) hx hmax (fun _ _ ↦ by simp [hzero])
  obtain ⟨y, hy, hfy⟩ := hpositive
  have hsame := hconstant hy
  change -f y = -f x at hsame
  linarith

/-- A nonnegative classical superharmonic function on a connected open domain
is strictly positive if it is positive at one point. No boundedness or boundary
condition is required. -/
theorem pos_of_nonneg_of_neg_laplacian_nonneg
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) {f : ℝ^n → ℝ}
    (hreg : ∀ x ∈ Ω, ContDiffAt ℝ 2 f x)
    (hnonneg : ∀ x ∈ Ω, 0 ≤ f x)
    (hsuper : ∀ x ∈ Ω, 0 ≤ -laplacian f x)
    (hpositive : ∃ y ∈ Ω, 0 < f y) :
    ∀ x ∈ Ω, 0 < f x :=
  pos_of_nonneg_of_neg_laplacian_add_mul_nonneg hΩ hconn (c := 0)
    hreg hnonneg (by simpa using hsuper) hpositive

end EllipticMaximum
