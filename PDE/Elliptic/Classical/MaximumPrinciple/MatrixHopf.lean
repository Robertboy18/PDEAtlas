/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixSymmetrization
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Hopf's boundary point lemma for arbitrary real matrices

For `Lu = -∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + Du[b] + cu`, a strict boundary maximum on an interior tangent ball forces
a negative inward one-sided derivative and a positive outward normal derivative. These are local
interior-ball forms of Hopf's Lemma in Evans's §6.4.2, where the real principal matrix need not be
symmetric. Its self-adjoint part has the same quadratic form, trace, and classical residual, and
Mathlib's positive matrix factorization supplies the directions used by the factored Hopf theorem.

Uniform quadratic ellipticity, upper trace and drift bounds, and `0 ≤ c ≤ C` are required only on
the outer annulus `R / 2 < ‖x - z‖ < R`. The subsolution inequality and compatibility condition
`c(x) u(x₀) ≥ 0` are also confined to this annulus. Thus the boundary maximum can have either sign
when the potential vanishes there. No coefficient continuity or bound on the antisymmetric part is
required.

## Main results

* `matrix_hopf_inward_deriv_neg`: the inward one-sided derivative is negative.
* `matrix_hopf_normal_fderiv_pos`: the derivative along the outward unit normal is positive.

## Implementation notes

The annulus reduction replaces every coefficient by zero off the annulus and subtracts the boundary
maximum from the function. The resulting factored residual is zero inside the half-ball and
nonpositive on the annulus. The radial barrier and Hopf proof of `MaximumPrinciple.Hopf` then apply
without extending any coefficient hypothesis to the half-ball.

The function remains continuous on the closed ball, `C²` in the open ball, and strictly below its
boundary value throughout that open ball. The one-sided formulation needs only the inward radial
derivative. The normal formulation assumes differentiability at the tangent point and uses the
ball's outward unit normal `R⁻¹ • (x₀ - z)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.4.2, Hopf's Lemma and its proof, pp. 347-349.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace EllipticMaximum

open Metric PDE.Analysis Set
open scoped InnerProductSpace

variable {n : ℕ}

/-- A strict boundary maximum for an arbitrary real-matrix subsolution has negative
inward radial derivative. The matrix is uniformly elliptic in the quadratic-form sense
on the outer annulus; its trace, the drift norm, and the nonnegative potential have upper
bounds there. The condition `c(x)u(x₀) ≥ 0` replaces a sign restriction on the maximum.
Principal factors are constructed from the self-adjoint part of the matrix. -/
theorem matrix_hopf_inward_deriv_neg
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ) (z : ℝ^n)
    {R κ A B C : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (helliptic : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R →
      ∀ v : ℝ^n, κ * ‖v‖ ^ 2 ≤
        ∑ i : Fin n, ∑ j : Fin n, a x i j * v i * v j)
    (htrace : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R →
      (∑ i : Fin n, a x i i) ≤ A)
    (hdrift : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → ‖b x‖ ≤ B)
    (hpotential : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → 0 ≤ c x ∧ c x ≤ C)
    {u : ℝ^n → ℝ} {x₀ : ℝ^n} (hx₀ : ‖x₀ - z‖ = R)
    (hcM : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → 0 ≤ c x * u x₀)
    (hucont : ContinuousOn u (closedBall z R))
    (hureg : ∀ x ∈ ball z R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → matrixOperator a b c u x ≤ 0)
    (hstrict : ∀ x ∈ ball z R, u x < u x₀)
    {d : ℝ} (hderiv : HasDerivWithinAt
      (fun s : ℝ ↦ u (x₀ + s • (z - x₀))) d (Ioi 0) 0) :
    d < 0 := by
  classical
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  let S : Set (ℝ^n) := {x | R / 2 < ‖x - z‖ ∧ ‖x - z‖ < R}
  let s : ℝ^n → Matrix (Fin n) (Fin n) ℝ :=
    fun x ↦ (selfAdjointPart ℝ (a x) : Matrix (Fin n) (Fin n) ℝ)
  have hex : ∀ x, ∃ σ : Fin n → ℝ^n,
      ∀ _ : x ∈ S, ∀ i j, s x i j = ∑ k, σ k i * σ k j := by
    intro x
    by_cases hx : x ∈ S
    · have hquad : ∀ v : ℝ^n,
          0 ≤ ∑ i : Fin n, ∑ j : Fin n, a x i j * v i * v j :=
        fun v ↦ (mul_nonneg hκ.le (sq_nonneg ‖v‖)).trans
          (helliptic x hx.1 hx.2 v)
      obtain ⟨σ, hσ⟩ := exists_factors_of_posSemidef
        (posSemidef_selfAdjointPart_of_nonneg_quadratic (a x) hquad)
      exact ⟨σ, fun _ ↦ hσ⟩
    · exact ⟨fun _ ↦ 0, fun h ↦ False.elim (hx h)⟩
  choose σ hσ using hex
  refine hopf_inward_deriv_neg_of_nonneg_mul σ b c z hR hκ hA hB hC
    ?_ ?_ hdrift hpotential hx₀ hcM hucont hureg ?_ hstrict hderiv
  · intro x hxinner hxouter v
    have hx : x ∈ S := ⟨hxinner, hxouter⟩
    rw [sum_inner_sq_eq_matrix_quadratic (s x) (σ x) (hσ x hx)]
    change κ * ‖v‖ ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n,
      (selfAdjointPart ℝ (a x) : Matrix (Fin n) (Fin n) ℝ) i j * v i * v j
    rw [matrix_quadratic_selfAdjointPart]
    exact helliptic x hxinner hxouter v
  · intro x hxinner hxouter
    have hx : x ∈ S := ⟨hxinner, hxouter⟩
    rw [sum_norm_sq_eq_matrix_trace (s x) (σ x) (hσ x hx)]
    change (∑ i : Fin n,
      (selfAdjointPart ℝ (a x) : Matrix (Fin n) (Fin n) ℝ) i i) ≤ A
    simpa only [matrix_selfAdjointPart_apply_diag] using htrace x hxinner hxouter
  · intro x hxinner hxouter
    have hx : x ∈ S := ⟨hxinner, hxouter⟩
    have hxball : x ∈ ball z R :=
      mem_ball.mpr (by simpa only [dist_eq_norm] using hxouter)
    rw [← matrixOperator_eq_factoredOperator s σ b c (hureg x hxball) (hσ x hx)]
    change matrixOperator
      (fun y ↦ (selfAdjointPart ℝ (a y) : Matrix (Fin n) (Fin n) ℝ)) b c u x ≤ 0
    rw [matrixOperator_selfAdjointPart a b c (hureg x hxball)]
    exact hsub x hxinner hxouter

/-- At a compatible strict boundary maximum of an arbitrary real-matrix subsolution,
the derivative along the tangent ball's outward unit normal is strictly positive.
Only the outer annulus carries coefficient bounds and a differential inequality; at the
tangent point, differentiability of the function suffices. -/
theorem matrix_hopf_normal_fderiv_pos
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ) (z : ℝ^n)
    {R κ A B C : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (helliptic : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R →
      ∀ v : ℝ^n, κ * ‖v‖ ^ 2 ≤
        ∑ i : Fin n, ∑ j : Fin n, a x i j * v i * v j)
    (htrace : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R →
      (∑ i : Fin n, a x i i) ≤ A)
    (hdrift : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → ‖b x‖ ≤ B)
    (hpotential : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → 0 ≤ c x ∧ c x ≤ C)
    {u : ℝ^n → ℝ} {x₀ : ℝ^n} (hx₀ : ‖x₀ - z‖ = R)
    (hcM : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → 0 ≤ c x * u x₀)
    (hucont : ContinuousOn u (closedBall z R))
    (hureg : ∀ x ∈ ball z R, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → matrixOperator a b c u x ≤ 0)
    (hstrict : ∀ x ∈ ball z R, u x < u x₀)
    (hubdry : DifferentiableAt ℝ u x₀) :
    0 < fderiv ℝ u x₀ (R⁻¹ • (x₀ - z)) := by
  have hline : HasDerivAt (fun s : ℝ ↦ x₀ + s • (z - x₀)) (z - x₀) 0 := by
    let L : ℝ →L[ℝ] ℝ^n :=
      (ContinuousLinearMap.id ℝ ℝ).smulRight (z - x₀)
    have hlinear : HasDerivAt (fun s : ℝ ↦ L s) (L 1) 0 :=
      L.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_id (0 : ℝ))
    have h := (hasDerivAt_const_add_iff x₀).2 hlinear
    have hLone : L 1 = z - x₀ := by
      simp [L]
    rw [hLone] at h
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s ↦ by simp [L])
  have hdu : HasDerivAt (fun s : ℝ ↦ u (x₀ + s • (z - x₀)))
      (fderiv ℝ u x₀ (z - x₀)) 0 := by
    have hu' : HasFDerivAt u (fderiv ℝ u x₀) (x₀ + (0 : ℝ) • (z - x₀)) := by
      simpa using hubdry.hasFDerivAt
    exact hu'.comp_hasDerivAt 0 hline
  have hneg := matrix_hopf_inward_deriv_neg a b c z hR hκ hA hB hC
    helliptic htrace hdrift hpotential hx₀ hcM hucont hureg hsub hstrict
    hdu.hasDerivWithinAt
  rw [show z - x₀ = -(x₀ - z) by abel, map_neg] at hneg
  rw [map_smul, smul_eq_mul]
  exact mul_pos (inv_pos.mpr hR) (neg_lt_zero.mp hneg)

end EllipticMaximum
