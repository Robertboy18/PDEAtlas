/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Locally finite smooth sums on open domains

Local finiteness is needed only inside the domain. Restricting the functions to the open
submanifold gives smoothness of their sum without imposing any condition at boundary points.
This fact does not depend on a Sobolev graph or completeness of the codomain.
-/

@[expose] public noncomputable section

open Function Set TopologicalSpace
open scoped Manifold Topology

namespace SobolevSpace.Approximation.OpenDomain

/-- A sum with supports locally finite on an open domain is smooth there. The functions may
take values in any real normed space, and the index type need not be countable. -/
theorem contDiffOn_finsum_of_locallyFinite {n : ℕ} {ι F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Ω : Opens (ℝ^n))
    (f : ι → ℝ^n → F) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfin : LocallyFinite (fun i ↦ (Subtype.val : Ω → ℝ^n) ⁻¹' support (f i))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ ∑ᶠ i, f i x) Ω := by
  have hsub : ContMDiff 𝓘(ℝ, ℝ^n) 𝓘(ℝ, F) (⊤ : ℕ∞)
      (fun x : Ω ↦ ∑ᶠ i, f i x) := by
    apply contMDiff_finsum
    · intro i
      exact (hf i).contMDiff.comp contMDiff_subtype_val
    · exact hfin
  intro x hx
  exact ((contMDiffAt_subtype_iff (U := Ω) (f := fun x : ℝ^n ↦ ∑ᶠ i, f i x)).mp
    (hsub.contMDiffAt (x := ⟨x, hx⟩))).contDiffAt.contDiffWithinAt

end SobolevSpace.Approximation.OpenDomain
