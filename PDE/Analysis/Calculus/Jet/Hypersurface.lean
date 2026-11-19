/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jet.TangentTrace
public import PDE.Analysis.Geometry.Hypersurface.Conormal
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Differences of jets on a hypersurface

Equality of an entire derivative along a hypersurface forces the next
derivative difference to be a pure conormal tensor. This uses the derivative
of the actual local parametrization, without flattening the equation.
-/

@[expose] public section

open Filter Set
open scoped Topology ContDiff

namespace PDE.Analysis

variable {E F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The next jet difference of two maps with the same jet on a hypersurface
is a multiple of its conormal tensor. -/
theorem HasConormalParametrizations.iteratedFDeriv_sub_eq_prod_smul
    {Γ : Set E} {ℓ : E → E →ₗ[ℝ] ℝ}
    (hΓ : HasConormalParametrizations H Γ ℓ)
    {u v : E → F} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    {n : ℕ} (heq : ∀ y ∈ Γ, iteratedFDeriv ℝ n u y = iteratedFDeriv ℝ n v y)
    {x : E} (hx : x ∈ Γ) {e : E} (he : ℓ x e = 1)
    (w : Fin (n + 1) → E) :
    (iteratedFDeriv ℝ (n + 1) u x - iteratedFDeriv ℝ (n + 1) v x) w =
      (∏ i, ℓ x (w i)) •
        (iteratedFDeriv ℝ (n + 1) u x - iteratedFDeriv ℝ (n + 1) v x)
          (fun _ ↦ e) := by
  obtain ⟨ψ, z, ψ', hψx, hψ, hrange, hmem⟩ := hΓ x hx
  have hsub (i : ℕ) (y : E) :
      iteratedFDeriv ℝ i (u - v) y =
        iteratedFDeriv ℝ i u y - iteratedFDeriv ℝ i v y :=
    iteratedFDeriv_sub_apply (hu.contDiffAt.of_le (by simp))
      (hv.contDiffAt.of_le (by simp))
  have htrace : ∀ᶠ y in 𝓝 z, iteratedFDeriv ℝ n (u - v) (ψ y) = 0 := by
    filter_upwards [hmem] with y hy
    rw [hsub, heq _ hy, sub_self]
  have h := iteratedFDeriv_eq_prod_smul_of_tangent_trace (hu.sub hv)
    hψ (ℓ x) hrange he htrace w
  change iteratedFDeriv ℝ (n + 1) (u - v) (ψ z) w =
    (∏ i, ℓ x (w i)) • iteratedFDeriv ℝ (n + 1) (u - v) (ψ z) (fun _ ↦ e) at h
  rw [hψx, hsub] at h
  exact h

end PDE.Analysis
