/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
public import PDE.DistributionTheory.TestFunction.Partition

/-!
# Locality of weak first derivatives

Weak derivative identities on an open cover imply the identity on the whole
domain. A compactly supported test has a finite subordinate decomposition.
Linearity of the test-function derivative then assembles the identities,
including all partition derivatives, without extra regularity of the state.
-/

@[expose] public noncomputable section

open PDE (partialDeriv)

open MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace SobolevSpace

variable {n : ℕ} {ι : Type*} {Ω : Set (ℝ^n)} {f g : ℝ^n → ℝ}

/-- First weak derivatives are local on any open cover of the domain. -/
theorem hasWeakDerivativeOn_single_of_open_cover
    (U : ι → Set (ℝ^n)) (hU : ∀ j, IsOpen (U j))
    (hcover : Ω ⊆ ⋃ j, U j)
    (i : Fin n) (hweak : ∀ j, HasWeakDerivativeOn (U j) [i] f g) :
    HasWeakDerivativeOn Ω [i] f g := by
  classical
  have hloc {a : ℝ^n → ℝ} (ha : ∀ j, LocallyIntegrableOn a (U j) volume) :
      LocallyIntegrableOn a Ω volume := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
    have h := ha j x hj
    rw [(hU j).nhdsWithin_eq hj] at h
    exact h.filter_mono nhdsWithin_le_nhds
  refine ⟨hloc (fun j ↦ (hweak j).locallyIntegrable_f),
    hloc (fun j ↦ (hweak j).locallyIntegrable_g), ?_⟩
  intro φ hφ
  obtain ⟨s, ψ, hψ, hsum⟩ :=
    TestFunction.exists_finset_sum_subordinate φ U hU (hφ.trans hcover)
  have hsuppL (j : ι) :
      Function.support (fun x ↦ f x * (∂[i] (ψ j : ℝ^n → ℝ)) x) ⊆ U j :=
    (Function.support_mul_subset_right _ _).trans
      ((subset_tsupport _).trans
        ((tsupport_iteratedPartialDeriv_subset_tsupport [i] (ψ j)).trans (hψ j)))
  have hsuppR (j : ι) : Function.support (fun x ↦ g x * ψ j x) ⊆ U j :=
    (Function.support_mul_subset_right _ _).trans ((subset_tsupport _).trans (hψ j))
  have hIL (j : ι) : Integrable (fun x ↦ f x * (∂[i] (ψ j : ℝ^n → ℝ)) x) volume :=
    (integrableOn_iff_integrable_of_support_subset (hsuppL j)).mp
      ((hweak j).integrable_mul_iteratedPartialDeriv (ψ j) (hψ j))
  have hIR (j : ι) : Integrable (fun x ↦ g x * ψ j x) volume :=
    (integrableOn_iff_integrable_of_support_subset (hsuppR j)).mp
      ((hweak j).integrable_mul_testFunction (ψ j) (hψ j))
  have hset (a : ℝ^n → ℝ) {V : Set (ℝ^n)} (ha : Function.support a ⊆ V) :
      (∫ x in V, a x) = ∫ x, a x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      by_contra hax
      exact hx (ha hax)
  have hpair (j : ι) :
      (∫ x, f x * (∂[i] (ψ j : ℝ^n → ℝ)) x) = -(∫ x, g x * ψ j x) := by
    have h := (hweak j) (ψ j) (hψ j)
    change (∫ x in U j, f x * (∂[i] (ψ j : ℝ^n → ℝ)) x) =
      (-1 : ℝ) ^ 1 * ∫ x in U j, g x * ψ j x at h
    simpa only [pow_one, neg_one_mul, hset _ (hsuppL j), hset _ (hsuppR j)] using h
  have hsumD (x : ℝ^n) :
      (∂[i] (φ : ℝ^n → ℝ)) x = ∑ j ∈ s, (∂[i] (ψ j : ℝ^n → ℝ)) x := by
    have hD (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (v y : ℝ^n) :
        lineDeriv ℝ χ y v = fderiv ℝ χ y v :=
      (χ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv
    have heq := congrArg
      (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) :
        𝓓((⊤ : Opens (ℝ^n)), ℝ) →L[ℝ] 𝓓((⊤ : Opens (ℝ^n)), ℝ)) hsum
    have hfun := congrArg
      (FunLike.coeAddMonoidHom 𝓓((⊤ : Opens (ℝ^n)), ℝ) (ℝ^n) ℝ) heq
    simpa [FunLike.coeAddMonoidHom_apply, Finset.sum_apply,
      testFunction_lineDerivCLM_apply, partialDeriv, hD] using congrFun hfun x
  have hsumV (x : ℝ^n) : φ x = ∑ j ∈ s, ψ j x := by
    have hfun := congrArg
      (FunLike.coeAddMonoidHom 𝓓((⊤ : Opens (ℝ^n)), ℝ) (ℝ^n) ℝ) hsum
    simpa only [map_sum, FunLike.coeAddMonoidHom_apply, Finset.sum_apply] using
      congrFun hfun x
  have hleft : (∫ x in Ω, f x * (∂[i] (φ : ℝ^n → ℝ)) x) =
      ∫ x, f x * (∂[i] (φ : ℝ^n → ℝ)) x :=
    hset _ ((Function.support_mul_subset_right _ _).trans ((subset_tsupport _).trans
      ((tsupport_iteratedPartialDeriv_subset_tsupport [i] φ).trans hφ)))
  have hright : (∫ x in Ω, g x * φ x) = ∫ x, g x * φ x :=
    hset _ ((Function.support_mul_subset_right _ _).trans ((subset_tsupport _).trans hφ))
  change (∫ x in Ω, f x * (∂[i] (φ : ℝ^n → ℝ)) x) =
    (-1 : ℝ) ^ 1 * ∫ x in Ω, g x * φ x
  rw [pow_one, neg_one_mul, hleft, hright]
  simp_rw [hsumD, hsumV, Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ ↦ hIL j),
    integral_finsetSum _ (fun j _ ↦ hIR j), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ hpair j

end SobolevSpace
