/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.GradientReaction.Regularity

/-!
# An affine gradient reaction with a nonzero offset

For the affine gradient reaction `b(p) = c + ℓ(p)`, with `c ≠ 0` and `ℓ` continuous
linear, and `μ ≥ 1 + ‖ℓ‖²`, the problem `-Δu + b(∇u) + μu = 0` with zero boundary
values on a bounded `C²` domain has a unique weak solution in `H¹₀`. It lies in `H²`
and satisfies the equation almost everywhere (`existsUnique_h2_solution`). The
threshold on `μ` depends only on `‖ℓ‖`.
-/

@[expose] public section

noncomputable section

namespace PDE.Examples.GradientReaction

open SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.GradientReaction
open MeasureTheory
open scoped Sobolev

/-- For `c ≠ 0` and `μ ≥ 1 + ‖ℓ‖²`, the equation `-Δu + c + ℓ(∇u) + μu = 0` has a unique
weak solution in `H¹₀`, and it is an `H²` solution almost everywhere. -/
theorem exists_affine_solution (n : ℕ) (hn : 0 < n)
    (ℓ : ℝ^n →L[ℝ] ℝ) (μ : ℝ) (hμ : 1 + ‖ℓ‖ ^ 2 ≤ μ)
    (Ω : Set (ℝ^n)) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (c : ℝ) (hc : c ≠ 0) :
    (c + ℓ 0 ≠ 0) ∧ ContDiff ℝ ⊤ (fun p ↦ c + ℓ p) ∧
      ∃ (u : H¹₀(Ω)) (U : W^{2,2}(Ω)),
        IsWeakSolution (fun p ↦ c + ℓ p) μ u ∧
        wkpBaseCoordinateCLM U = baseCoordCLM u ∧
        lowerOrderCLM (k := 1) (m := 2) (by omega) U = h10SubtypeL u ∧
        (∀ᵐ x ∂domainMeasure n Ω,
          -(∑ i : Fin n, U.val (pairDerivIndex n i i) x) +
            (c + ℓ (∇ (u : H¹(Ω)) x)) + μ * baseCoordCLM u x = 0) ∧
        ∀ v : H¹₀(Ω), IsWeakSolution (fun p ↦ c + ℓ p) μ v → v = u := by
  let : Fact (0 < n) := ⟨hn⟩
  have hb : LipschitzWith ‖ℓ‖₊ (fun p ↦ c + ℓ p) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simpa only [dist_add_left] using ℓ.lipschitzWith.dist_le_mul p q
  obtain ⟨u, ⟨hu, U, hbase, hfirst, _, _, hae⟩, huniq⟩ :=
    existsUnique_h2_solution n hn ‖ℓ‖₊ μ hμ Ω hopen hbounded hgraph (fun p ↦ c + ℓ p) hb
  refine ⟨by simpa using hc, by fun_prop, u, U, hu, hbase, hfirst, hae, ?_⟩
  intro v hv
  exact huniq v ⟨hv, exists_h2_of_isWeakSolution hopen hbounded hgraph hb μ v hv⟩

end PDE.Examples.GradientReaction
