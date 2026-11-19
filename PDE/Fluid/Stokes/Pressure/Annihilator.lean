/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Variational.Residual
import PDE.Analysis.LinearAlgebra.Factorization
import PDE.DistributionTheory.TestFunction.Derivative.Commutation

/-!
# Algebraic pressure from the Stokes minimum

The first variation vanishes on the entire kernel of divergence. It therefore
factors algebraically through divergence, without a range-closedness assumption.
On scalar tests this factor has the residual as its negative derivative.
Local Sobolev regularity is established separately before interpreting it as pressure.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions Sobolev ENNReal RealInnerProductSpace

namespace IncompressibleFlow.Stokes

open SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace

variable {n : ℕ} {Ω : Opens (ℝ^n)}

private theorem load_single_test
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω))
    (j : Fin n) (φ : TestFunctionOn n (Ω : Set (ℝ^n))) :
    ⟪f, toLp (ofTestFunction (Pi.single j φ))⟫ =
      ∫ x in (Ω : Set (ℝ^n)), f x j * φ.1 x := by
  classical
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [toLp_ofTestFunction_apply_ae (Pi.single j φ)] with x hx
  have hval : toLp (ofTestFunction (Pi.single j φ)) x =
      EuclideanSpace.single j (φ.1 x) := by
    ext i
    rw [hx i]
    by_cases hij : i = j
    · subst i
      simp
    · simp [hij]
  rw [hval, EuclideanSpace.inner_single_right]
  simp [mul_comm]

/-- The full divergence-free minimum produces an algebraic scalar functional
whose distributional coordinate derivatives are the Stokes residual.
This step requires neither domain topology nor a divergence right inverse. -/
theorem exists_linearMap_partialDeriv_eq_neg_residual_of_minimizes_energy
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) (u : H¹₀(Ω; ℝ^n))
    (hu : ∇· u = 0)
    (hmin : ∀ w : H¹₀(Ω; ℝ^n), ∇· w = 0 →
      energy f u ≤ energy f w) :
    ∃ q : 𝓓((⊤ : Opens (ℝ^n)), ℝ) →ₗ[ℝ] ℝ,
      ∀ j : Fin n, ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
        ∀ hφ : tsupport φ ⊆ Ω,
          q (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j (1 : ℝ)) φ) =
            -residual f u j ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩ := by
  let ell : H¹₀(Ω; ℝ^n) →ₗ[ℝ] ℝ :=
    ((innerSL ℝ (∇ u)).comp gradient -
      (innerSL ℝ f).comp toLp).toLinearMap
  have hker : divergence.toLinearMap.ker ≤ ell.ker := by
    intro v hv
    change ⟪∇ u, ∇ v⟫ - ⟪f, toLp v⟫ = 0
    exact sub_eq_zero.mpr (stationary_of_minimizes_energy f u hu hmin v hv)
  obtain ⟨g, hg⟩ := LinearMap.exists_comp_eq_of_ker_le
    divergence.toLinearMap ell hker
  let Q : TestFunctionOn n (Ω : Set (ℝ^n)) →ₗ[ℝ] ℝ :=
    g.comp (baseCoordCLM.toLinearMap.comp testFunctionToH10Linear)
  obtain ⟨q, hq⟩ := Q.exists_extend
  refine ⟨q, fun j φ hφ ↦ ?_⟩
  let ψ : TestFunctionOn n (Ω : Set (ℝ^n)) := ⟨φ, hφ⟩
  have hderiv : (ψ.iteratedPartialDeriv [j]).1 =
      TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j (1 : ℝ)) φ := by
    ext x
    rw [TestFunction.lineDerivCLM_apply_eq_fderiv]
    rfl
  have hbase : baseCoordCLM (testFunctionToH10Linear (ψ.iteratedPartialDeriv [j])) =
      derivCoordCLM j (testFunctionToH10 ψ) := by
    change baseCoordCLM (testFunctionToH10 (ψ.iteratedPartialDeriv [j])) = _
    apply Lp.ext
    filter_upwards [baseCoordCLM_testFunction_apply_ae (ψ.iteratedPartialDeriv [j]),
      derivCoordCLM_testFunction_apply_ae j ψ] with x hx hy
    rw [hx, hy]
    rfl
  have hqeq := congrArg
    (fun L : TestFunctionOn n (Ω : Set (ℝ^n)) →ₗ[ℝ] ℝ ↦
      L (ψ.iteratedPartialDeriv [j])) hq
  change q (ψ.iteratedPartialDeriv [j]).1 =
    g (baseCoordCLM (testFunctionToH10Linear (ψ.iteratedPartialDeriv [j]))) at hqeq
  rw [hderiv, hbase, ← divergence_ofTestFunction_single] at hqeq
  have hgtest := congrArg (fun L : H¹₀(Ω; ℝ^n) →ₗ[ℝ] ℝ ↦
    L (ofTestFunction (Pi.single j ψ))) hg
  change g (∇· (ofTestFunction (Pi.single j ψ))) =
    ⟪∇ u, ∇ (ofTestFunction (Pi.single j ψ))⟫ -
      ⟪f, toLp (ofTestFunction (Pi.single j ψ))⟫ at hgtest
  rw [hqeq, hgtest, inner_gradient_ofTestFunction_single, load_single_test]
  simp only [inner_deriv_testFunction_eq_integral, residual_apply, neg_add_rev, neg_neg]
  change _ - _ = -_ + _
  rw [neg_add_eq_sub]
  rfl

end IncompressibleFlow.Stokes
