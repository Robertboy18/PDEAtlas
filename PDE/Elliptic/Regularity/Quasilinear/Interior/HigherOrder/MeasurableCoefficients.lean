/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Coefficients
import PDE.Analysis.MeasureTheory.Lp.EssentialSupremum

/-!
# Measurable coefficients at a weak gradient

A bounded positive Jacobian evaluated at an almost everywhere strongly
measurable field defines uniformly elliptic `L∞` coefficients. Applying this
to the gradient of a uniformly convex `C²` density supplies the coefficients
in the differentiated Euler–Lagrange equation of Evans §8.3.2.

Only measurability of the evaluation field is needed. In particular, the
construction applies to a Sobolev gradient before any continuity or
Hölder regularity has been established.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Gradient

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Evaluating a bounded positive Jacobian at a measurable field produces
bounded uniformly elliptic coefficient classes, with the same ellipticity
constant and an entrywise bound by the Lipschitz constant of the flux. -/
theorem exists_elliptic_jacobian_coefficients
    {A : ℝ^n → ℝ^n} (hA : ContDiff ℝ 1 A)
    {Λ : ℝ≥0} (hLip : LipschitzWith Λ A) {θ : ℝ} (hθ : 0 < θ)
    (hpositive : ∀ p z, θ * ‖z‖ ^ 2 ≤ ⟪fderiv ℝ A p z, z⟫)
    {g : ℝ^n → ℝ^n} (hg : AEStronglyMeasurable g (domainMeasure n Ω)) :
    ∃ B : Fin n → Fin n → DerivLp n ∞ Ω,
      (∀ i j, (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ jacobianMatrix A (g x) i j) ∧
      (∀ i j, ‖B i j‖ ≤ Λ) ∧ AEUniformlyElliptic B θ := by
  have hc (i j : Fin n) : Continuous (fun p ↦ jacobianMatrix A p i j) :=
    ((contDiff_pi.mp (contDiff_pi.mp (contDiff_jacobianMatrix (r := 0) hA) i)) j).continuous
  have hnorm (p : ℝ^n) (i j : Fin n) : ‖jacobianMatrix A p i j‖ ≤ Λ := by
    rw [jacobianMatrix_apply_eq_fderiv (hA.differentiable_one p)]
    exact (PiLp.norm_apply_le _ i).trans
      (((fderiv ℝ A p).le_opNorm _).trans
        (by simpa using norm_fderiv_le_of_lipschitz ℝ hLip (x₀ := p)))
  have hmem (i j : Fin n) :
      MemLp (fun x ↦ jacobianMatrix A (g x) i j) ∞ (domainMeasure n Ω) :=
    memLp_top_of_bound ((hc i j).comp_aestronglyMeasurable hg)
      Λ (Filter.Eventually.of_forall fun x ↦ hnorm (g x) i j)
  let B (i j : Fin n) : DerivLp n ∞ Ω := (hmem i j).toLp _
  have hrep (i j : Fin n) :
      (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ jacobianMatrix A (g x) i j := (hmem i j).coeFn_toLp
  refine ⟨B, hrep, ?_, hθ, ?_⟩
  · intro i j
    apply Lp.norm_top_le_of_ae_bound Λ.coe_nonneg
    exact (hrep i j).mono fun x hx ↦ by rw [hx]; exact hnorm (g x) i j
  · filter_upwards [ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hrep i)] with x hx
    intro ξ
    let z : ℝ^n := WithLp.toLp 2 ξ
    have h := hpositive (g x) z
    have henergy : ⟪fderiv ℝ A (g x) z, z⟫ =
        ∑ i, ∑ j, B i j x * ξ j * ξ i := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [← sum_jacobianMatrix_mul (hA.differentiable_one (g x)) z i]
      simp only [RCLike.inner_apply, RCLike.conj_to_real, z, hx, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    rw [henergy, EuclideanSpace.real_norm_sq_eq z] at h
    simpa only [z, pow_two] using h

/-- A uniformly bounded positive Hessian gives the linearized
coefficients at any measurable field. The density is only `C²`, and no
pointwise regularity of the field is required. -/
theorem exists_measurable_linearizedCoefficients_of_gradientDensity
    {L : ℝ^n → ℝ} (hL : ContDiff ℝ 2 L)
    {Λ : ℝ≥0} (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ)
    {θ : ℝ} (hθ : 0 < θ)
    (hpositive : ∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z)
    {g : ℝ^n → ℝ^n} (hg : AEStronglyMeasurable g (domainMeasure n Ω)) :
    ∃ B : Fin n → Fin n → DerivLp n ∞ Ω,
      (∀ i j, (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ jacobianMatrix (∇ L) (g x) i j) ∧
      (∀ i j, ‖B i j‖ ≤ Λ) ∧ AEUniformlyElliptic B θ := by
  apply exists_elliptic_jacobian_coefficients (contDiff_gradient_of_contDiff_two hL)
    (lipschitzWith_gradient_of_hessian_bound hL hbound) hθ _ hg
  intro p z
  rw [inner_fderiv_gradient_at hL.contDiffAt]
  exact hpositive p z

end PDE.Elliptic.Regularity.Quasilinear
