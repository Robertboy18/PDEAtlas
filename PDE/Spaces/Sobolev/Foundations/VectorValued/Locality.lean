/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.VectorValued.WeakDerivatives

/-!
# Locality of Banach-valued weak derivatives

Weak derivative identities on relatively compact open subdomains determine the identity
on the whole domain, since every test function has compact support inside the domain.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace SobolevSpace.VectorValued

variable {n : ℕ} {Ω : Opens ℝ^n} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Weak derivative identities on every relatively compact open subdomain determine
the identity on the whole domain. -/
theorem hasWeakDerivativeOn_of_relativelyCompact {f g : ℝ^n → F} {α : List (Fin n)}
    (hf : LocallyIntegrableOn f Ω volume) (hg : LocallyIntegrableOn g Ω volume)
    (hlocal : ∀ U : Opens ℝ^n, IsCompact (closure (U : Set ℝ^n)) →
      closure (U : Set ℝ^n) ⊆ Ω → HasWeakDerivativeOn U α f g) :
    HasWeakDerivativeOn Ω α f g := by
  refine ⟨hf, hg, ?_⟩
  intro φ
  obtain ⟨U, hU, hφU, hclU, hcompact⟩ :=
    exists_open_between_and_isCompact_closure φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
  let V : Opens ℝ^n := ⟨U, hU⟩
  let ψ : 𝓓(V, ℝ) := ⟨φ.toFun, φ.contDiff, φ.hasCompactSupport, hφU⟩
  have h := (hlocal V hcompact hclU).integral_identity ψ
  have hlφ : (∫ x, iteratedPartialDeriv α φ.toFun x • f x) =
      ∫ x, iteratedPartialDeriv α φ.toFun x • f x ∂domainMeasure n Ω :=
    integral_smul_test_eq_setIntegral f (iteratedPartialDerivTest α φ)
  have hlψ : (∫ x, iteratedPartialDeriv α ψ.toFun x • f x) =
      ∫ x, iteratedPartialDeriv α ψ.toFun x • f x ∂domainMeasure n V :=
    integral_smul_test_eq_setIntegral f (iteratedPartialDerivTest α ψ)
  have hrφ := integral_smul_test_eq_setIntegral g φ
  have hrψ := integral_smul_test_eq_setIntegral g ψ
  rw [← hlφ, ← hrφ]
  rw [← hlψ, ← hrψ] at h
  exact h

end SobolevSpace.VectorValued
