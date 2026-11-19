/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
import PDE.Analysis.Calculus.Support.Parametric

/-!
# Uniform bounds for spatial derivatives of a parameter family

Spatial differentiation preserves joint support. Applying Mathlib’s compact-support
bound to the family and its derivatives therefore gives bounds independent of the parameter.
-/

@[expose] public section

open Set Topology

namespace PDE.FDeriv

variable {n : ℕ}

/-- Compact support and continuity give uniform bounds for a family and all its first and second
coordinate derivatives. The parameter space needs only a topology. -/
theorem exists_uniform_spatial_jet_bounds
    {S E : Type*} [TopologicalSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : S × ℝ^n → E) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfirst : ∀ i : Fin n, Continuous
      (fun p : S × ℝ^n ↦ (∂[i] (fun x ↦ f (p.1, x))) p.2))
    (hsecond : ∀ i j : Fin n, Continuous
      (fun p : S × ℝ^n ↦
        (∂[i] (∂[j] (fun x ↦ f (p.1, x)))) p.2)) :
    ∃ (M : ℝ) (C : Fin n → ℝ) (B : Fin n → Fin n → ℝ),
      (∀ p, ‖f p‖ ≤ M) ∧
      (∀ i (p : S × ℝ^n), ‖(∂[i] (fun x ↦ f (p.1, x))) p.2‖ ≤ C i) ∧
      ∀ i j (p : S × ℝ^n), ‖(∂[i] (∂[j] (fun x ↦ f (p.1, x)))) p.2‖ ≤
        B i j := by
  have hfirstc (i : Fin n) : HasCompactSupport
      (fun p : S × ℝ^n ↦ (∂[i] (fun x ↦ f (p.1, x))) p.2) :=
    hfc.fderiv_snd_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hsecondc (i j : Fin n) : HasCompactSupport
      (fun p : S × ℝ^n ↦
        (∂[i] (∂[j] (fun x ↦ f (p.1, x)))) p.2) :=
    (hfirstc j).fderiv_snd_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  choose C hC using fun i ↦ (hfirst i).bounded_above_of_compact_support (hfirstc i)
  choose B hB using fun i j ↦ (hsecond i j).bounded_above_of_compact_support (hsecondc i j)
  exact ⟨M, C, B, hM, hC, hB⟩

end PDE.FDeriv
