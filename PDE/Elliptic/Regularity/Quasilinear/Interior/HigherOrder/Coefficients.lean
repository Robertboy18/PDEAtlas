/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Gradient.HessianBounds
public import PDE.Analysis.Calculus.Jacobian.Calculus
public import PDE.Elliptic.Variational.DivergenceForm
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Coefficients obtained by linearizing a gradient density

For a `C³` density and a locally Lipschitz gradient representative `g`, the
Jacobian `D(∇L)(g)` has locally Lipschitz entries. Uniform bounds and positivity of
the Hessian give bounded coefficient classes and uniform ellipticity. These are
the coefficients in the differentiated Euler–Lagrange equation of Evans §8.3.2.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A `C³` density has a `C²` gradient, with its Riesz representation. -/
theorem contDiff_two_gradient_of_contDiff_three {L : ℝ^n → ℝ}
    (hL : ContDiff ℝ 3 L) : ContDiff ℝ 2 (∇ L) := by
  let R := (InnerProductSpace.toDual ℝ (ℝ^n)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact R.contDiff.comp (hL.fderiv_right (m := 2) (by norm_num))

/-- Applying the Jacobian to a vector gives the coordinate formula used
in the divergence-form coefficient operator. -/
theorem sum_jacobianMatrix_mul {A : ℝ^n → ℝ^n} {p : ℝ^n}
    (hA : DifferentiableAt ℝ A p) (v : ℝ^n) (i : Fin n) :
    (∑ j, jacobianMatrix A p i j * v j) = fderiv ℝ A p v i := by
  calc
    _ = fderiv ℝ (fun z ↦ A z i) p v :=
      (fderiv_apply_eq_sum_partialDeriv_mul _ p v).symm
    _ = _ := congrArg (fun T : ℝ^n →L[ℝ] ℝ ↦ T v)
      (((EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).hasFDerivAt.comp p hA.hasFDerivAt).fderiv)

/-- Linearization at a locally Lipschitz gradient produces bounded, uniformly
elliptic coefficients and derives their local Lipschitz regularity. -/
theorem exists_linearizedCoefficients_of_gradientDensity
    (hΩ : IsOpen Ω) {L : ℝ^n → ℝ} (hL : ContDiff ℝ 3 L)
    {Λ : ℝ≥0} (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ)
    {θ : ℝ} (hθ : 0 < θ)
    (hpositive : ∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z)
    {g : ℝ^n → ℝ^n} (hg : LocallyLipschitzOn Ω g) :
    ∃ B : Fin n → Fin n → DerivLp n ∞ Ω,
      (∀ i j, (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ jacobianMatrix (∇ L) (g x) i j) ∧
      (∀ i j, LocallyLipschitzOn Ω (fun x ↦ jacobianMatrix (∇ L) (g x) i j)) ∧
      AEUniformlyElliptic B θ := by
  have hL2 : ContDiff ℝ 2 L := hL.of_le (by norm_num)
  have hA := contDiff_two_gradient_of_contDiff_three hL
  have hLip := lipschitzWith_gradient_of_hessian_bound hL2 hbound
  have hc (i j : Fin n) : ContDiff ℝ 1 (fun p ↦ jacobianMatrix (∇ L) p i j) :=
    (contDiff_pi.mp (contDiff_pi.mp (contDiff_jacobianMatrix (r := 1) hA) i)) j
  have hlocal (i j : Fin n) :
      LocallyLipschitzOn Ω (fun x ↦ jacobianMatrix (∇ L) (g x) i j) :=
    locallyLipschitzOn_iff_restrict.mpr ((hc i j).locallyLipschitz.comp hg.restrict)
  have hnorm (p : ℝ^n) (i j : Fin n) : ‖jacobianMatrix (∇ L) p i j‖ ≤ Λ := by
    rw [jacobianMatrix_apply_eq_fderiv (hA.differentiable (by norm_num) p)]
    exact (PiLp.norm_apply_le _ i).trans
      (((fderiv ℝ (∇ L) p).le_opNorm _).trans
        (by simpa using norm_fderiv_le_of_lipschitz ℝ hLip (x₀ := p)))
  have hmem (i j : Fin n) :
      MemLp (fun x ↦ jacobianMatrix (∇ L) (g x) i j) ∞ (domainMeasure n Ω) :=
    memLp_top_of_bound ((hlocal i j).continuousOn.aestronglyMeasurable hΩ.measurableSet)
      Λ (Filter.Eventually.of_forall fun x ↦ hnorm (g x) i j)
  let B (i j : Fin n) : DerivLp n ∞ Ω := (hmem i j).toLp _
  have hrep (i j : Fin n) :
      (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ jacobianMatrix (∇ L) (g x) i j := (hmem i j).coeFn_toLp
  refine ⟨B, hrep, hlocal, hθ, ?_⟩
  filter_upwards [ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hrep i)] with x hx
  intro ξ
  let z : ℝ^n := WithLp.toLp 2 ξ
  have h := hpositive (g x) z
  rw [← inner_fderiv_gradient_at hL2.contDiffAt] at h
  have henergy :
      ⟪fderiv ℝ (∇ L) (g x) z, z⟫ =
        ∑ i, ∑ j, B i j x * ξ j * ξ i := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [← sum_jacobianMatrix_mul (hA.differentiable (by norm_num) (g x)) z i]
    simp only [RCLike.inner_apply, RCLike.conj_to_real, z, hx, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  rw [henergy, EuclideanSpace.real_norm_sq_eq z] at h
  simpa only [z, pow_two] using h

end PDE.Elliptic.Regularity.Quasilinear
