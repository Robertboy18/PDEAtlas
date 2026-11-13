/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates
public import PDE.FDeriv.Operators

/-!
# The distributional Laplacian of an H¹ function

Testing each weak first derivative against a derivative of a smooth compact
test identifies the Dirichlet pairing with the negative distributional
Laplacian. This shared identity is used in both directions: distributional
Poisson equations give energy equations, and weak harmonic fields satisfy
the hypotheses of Weyl's lemma.
-/

@[expose] public noncomputable section

open PDE (laplacian iteratedPartialDeriv)

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions InnerProductSpace Sobolev

namespace SobolevSpace.GraphSpace

/-- The Dirichlet pairing of an H¹ field with a compact smooth test is
the negative integral of the field against the Laplacian of that test. -/
theorem sum_inner_deriv_test_eq_neg_integral_laplacian
    {n : ℕ} {Ω : Set ℝ^n} (u : H¹(Ω)) (φ : TestFunctionOn n Ω) :
    (∑ i : Fin n, ⟪(u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i),
      derivCoordCLM i (testFunctionToH10 φ)⟫_ℝ) =
        -(∫ x, baseRepresentative u x * laplacian φ.1.toFun x ∂domainMeasure n Ω) := by
  let du (i : Fin n) : DerivLp n 2 Ω :=
    (u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i)
  have hw (i : Fin n) :
      HasWeakDerivativeOn Ω [i] (baseRepresentative u) (du i) := by
    simpa only [baseRepresentative, du, firstDerivIndex_one] using
      u.property.hasWeakDerivativeOn_first (by norm_num) i
  let dφ (i : Fin n) : 𝓓((⊤ : Opens (ℝ^n)), ℝ) := {
    toFun := (∂[i] φ.1.toFun)
    contDiff' := by
      simpa only [iteratedPartialDeriv, TestFunction.toFun_eq_coe] using
        PDE.contDiff_top_iteratedPartialDeriv φ.1.contDiff [i]
    hasCompactSupport' := by
      simpa only [iteratedPartialDeriv] using
        iteratedPartialDeriv_hasCompactSupport φ.1 [i]
    tsupport_subset' := subset_univ _
  }
  have hdφ (i : Fin n) : tsupport (dφ i).toFun ⊆ Ω :=
    (show tsupport (∂[i] φ.1.toFun) ⊆ tsupport φ.1.toFun by
      simpa only [iteratedPartialDeriv] using
        tsupport_iteratedPartialDeriv_subset_tsupport [i] φ.1.toFun).trans φ.2
  have hi (i : Fin n) :
      Integrable (fun x ↦ baseRepresentative u x *
        (∂[i] (∂[i] φ.1.toFun)) x) (domainMeasure n Ω) := by
    simpa only [iteratedPartialDeriv] using
      (hw i).integrable_mul_iteratedPartialDeriv (dφ i) (hdφ i)
  have hpair (i : Fin n) :
      ⟪du i, derivCoordCLM i (testFunctionToH10 φ)⟫_ℝ =
        -(∫ x, baseRepresentative u x *
          (∂[i] (∂[i] φ.1.toFun)) x ∂domainMeasure n Ω) := by
    have h := hw i (dφ i) (hdφ i)
    simp only [iteratedPartialDeriv, List.length_cons, List.length_nil,
      Nat.zero_add, pow_one, neg_one_mul] at h
    have hinner :
        ⟪du i, derivCoordCLM i (testFunctionToH10 φ)⟫_ℝ =
          ∫ x, (du i : ℝ^n → ℝ) x * (∂[i] φ.1.toFun) x
            ∂domainMeasure n Ω := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [derivCoordCLM_testFunction_apply_ae i φ] with x hx
      rw [hx]
      simp [RCLike.inner_apply, mul_comm]
    rw [hinner, h]
    simp only [neg_neg, dφ]
  have hsum :
      (∫ x, baseRepresentative u x * laplacian φ.1.toFun x ∂domainMeasure n Ω) =
        ∑ i : Fin n, ∫ x, baseRepresentative u x *
          (∂[i] (∂[i] φ.1.toFun)) x ∂domainMeasure n Ω := by
    simp only [laplacian, Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ ↦ hi i)
  change (∑ i, ⟪du i, derivCoordCLM i (testFunctionToH10 φ)⟫_ℝ) = _
  simp only [hpair, Finset.sum_neg_distrib, ← hsum]

end SobolevSpace.GraphSpace
