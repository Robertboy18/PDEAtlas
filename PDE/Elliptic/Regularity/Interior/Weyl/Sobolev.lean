/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Weyl
public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.LaplacianTest

/-!
# Classical harmonic representatives of weak harmonic fields

The Dirichlet identity implies the distributional Laplace equation by
integration by parts against a derivative of each test. Weyl's lemma then
constructs a classical harmonic representative of the same Sobolev class.
No boundary condition or prior continuous representative is required.
-/

@[expose] public noncomputable section

open PDE (laplacian iteratedPartialDeriv)

open scoped Sobolev

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions InnerProductSpace

namespace SobolevSpace.GraphSpace

/-- An H¹ field with zero Dirichlet pairing against H¹₀ has a
classical harmonic representative on any open domain of positive dimension. -/
theorem exists_isHarmonicPDE_ae_eq_of_dirichlet_eq_zero
    {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n} (hΩ : IsOpen Ω)
    (U : H¹(Ω))
    (hweak : ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex n i) U)
        (derivCoordCLM i t)) = 0) :
    ∃ u : ℝ^n → ℝ, LaplacianEquation.IsHarmonicPDE n u Ω ∧
      baseRepresentative U =ᵐ[domainMeasure n Ω] u := by
  have hu : LocallyIntegrableOn (baseRepresentative U) Ω volume :=
    memLp_locallyIntegrableOn_domain
      (Lp.memLp ((U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))) (by norm_num)
  apply LaplacianEquation.exists_isHarmonicPDE_ae_eq_of_integral_laplacian_eq_zero
    (Ω := ⟨Ω, hΩ⟩) hu
  intro φ
  let ψ₀ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) := TestFunction.monoCLM ℝ φ
  have hψ : ψ₀.toFun = (φ : ℝ^n → ℝ) := by
    simp only [TestFunction.toFun_eq_coe, ψ₀, TestFunction.monoCLM_apply,
      le_refl, le_top, and_self, ite_true]
  let ψ : TestFunctionOn n Ω := ⟨ψ₀, by
    change tsupport ψ₀.toFun ⊆ Ω
    rw [hψ]
    exact φ.tsupport_subset⟩
  have hzero :
      (∫ x, baseRepresentative U x * laplacian (φ : ℝ^n → ℝ) x
        ∂domainMeasure n Ω) = 0 := by
    have h := sum_inner_deriv_test_eq_neg_integral_laplacian U ψ
    have ht := hweak (testFunctionToH10 ψ)
    simp only [wkpCoordinateCLM_apply] at ht
    have := neg_eq_zero.mp (h.symm.trans ht)
    simpa only [ψ, hψ] using this
  rw [← hzero]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hxφ : x ∉ tsupport (φ : ℝ^n → ℝ) := fun h ↦ hx (φ.tsupport_subset h)
  have hΔ : laplacian (φ : ℝ^n → ℝ) x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hxd : x ∉ tsupport (∂[i] (φ : ℝ^n → ℝ)) := fun h ↦ hxφ
      ((show tsupport (∂[i] (φ : ℝ^n → ℝ)) ⊆ tsupport (φ : ℝ^n → ℝ) by
        simpa only [iteratedPartialDeriv] using
          tsupport_iteratedPartialDeriv_subset_tsupport [i] (φ : ℝ^n → ℝ)) h)
    change (fderiv ℝ (∂[i] (φ : ℝ^n → ℝ)) x) (EuclideanSpace.single i 1) = 0
    rw [fderiv_of_notMem_tsupport ℝ hxd]
    rfl
  simp only [hΔ, mul_zero]

end SobolevSpace.GraphSpace
