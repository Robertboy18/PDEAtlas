/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Local parametrizations and conormals

The differential of a hypersurface parametrization has range equal to the
kernel of its conormal. This description needs neither an orientation nor a
choice of global coordinates. It is preserved on relatively open pieces.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE.Analysis

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- At each point of `Γ`, a differentiable map from `H` locally takes values in `Γ`
and its differential has range equal to the prescribed conormal kernel.

These are first-order parametrization data; local injectivity and a coordinate inverse
are not required. -/
def HasConormalParametrizations (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Γ : Set E) (ℓ : E → E →ₗ[ℝ] ℝ) : Prop :=
  ∀ x ∈ Γ, ∃ (ψ : H → E) (z : H) (ψ' : H →L[ℝ] E),
    ψ z = x ∧ HasFDerivAt ψ ψ' z ∧
      LinearMap.range ψ'.toLinearMap = LinearMap.ker (ℓ x) ∧
        ∀ᶠ y in 𝓝 z, ψ y ∈ Γ

/-- Restricting to an open part of the ambient space preserves the same
parametrizations and conormals. -/
theorem HasConormalParametrizations.inter_open
    {Γ s : Set E} {ℓ : E → E →ₗ[ℝ] ℝ}
    (hΓ : HasConormalParametrizations H Γ ℓ) (hs : IsOpen s) :
    HasConormalParametrizations H (Γ ∩ s) ℓ := by
  intro x hx
  obtain ⟨ψ, z, ψ', hψx, hψ, hrange, hmem⟩ := hΓ x hx.1
  refine ⟨ψ, z, ψ', hψx, hψ, hrange, ?_⟩
  have hsψ : ∀ᶠ y in 𝓝 z, ψ y ∈ s :=
    hψ.continuousAt.preimage_mem_nhds (hs.mem_nhds (hψx ▸ hx.2))
  exact hmem.and hsψ

/-- Transport of local parametrizations by an invertible linear coordinate
change. The conormal is pulled back by its inverse. -/
theorem HasConormalParametrizations.map
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Γ : Set E} {ℓ : E → E →ₗ[ℝ] ℝ}
    (hΓ : HasConormalParametrizations H Γ ℓ) (A : E ≃L[ℝ] F) :
    HasConormalParametrizations H (A '' Γ)
      (fun y ↦ (ℓ (A.symm y)).comp A.symm.toLinearMap) := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨ψ, z, ψ', hψx, hψ, hrange, hmem⟩ := hΓ x hx
  refine ⟨A ∘ ψ, z, A.toContinuousLinearMap.comp ψ',
    congrArg A hψx, A.toContinuousLinearMap.hasFDerivAt.comp z hψ, ?_, ?_⟩
  · ext w
    simp only [A.symm_apply_apply, LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · rintro ⟨v, rfl⟩
      change ℓ x (A.symm (A (ψ' v))) = 0
      rw [A.symm_apply_apply]
      have hv : ψ' v ∈ LinearMap.range ψ'.toLinearMap := ⟨v, rfl⟩
      rw [hrange] at hv
      exact hv
    · intro hw
      have hw' : A.symm w ∈ LinearMap.range ψ'.toLinearMap := by
        rw [hrange]
        exact hw
      obtain ⟨v, hv⟩ := hw'
      refine ⟨v, ?_⟩
      change A (ψ' v) = w
      change ψ' v = A.symm w at hv
      rw [hv, A.apply_symm_apply]
  · filter_upwards [hmem] with v hv
    exact ⟨ψ v, hv, rfl⟩

/-- A differentiable graph has the usual conormal `dt - Dg dx`. This supplies
curved examples directly from the graph function and its derivative. -/
theorem hasConormalParametrizations_graph
    {g : H → ℝ} (hg : Differentiable ℝ g) :
    HasConormalParametrizations H (range fun y ↦ (y, g y))
      (fun x : H × ℝ ↦
        (ContinuousLinearMap.snd ℝ H ℝ -
          (fderiv ℝ g x.1).comp (ContinuousLinearMap.fst ℝ H ℝ)).toLinearMap) := by
  rintro x ⟨z, rfl⟩
  refine ⟨fun y ↦ (y, g y), z,
    (ContinuousLinearMap.id ℝ H).prod (fderiv ℝ g z), rfl,
    (hasFDerivAt_id z).prodMk (hg z).hasFDerivAt, ?_, ?_⟩
  · ext w
    constructor
    · rintro ⟨y, rfl⟩
      simp
    · intro hw
      change w.2 - fderiv ℝ g z w.1 = 0 at hw
      refine ⟨w.1, ?_⟩
      change (w.1, fderiv ℝ g z w.1) = w
      exact Prod.ext rfl (sub_eq_zero.mp hw).symm
  · exact Filter.Eventually.of_forall fun y ↦ ⟨y, rfl⟩

end PDE.Analysis
