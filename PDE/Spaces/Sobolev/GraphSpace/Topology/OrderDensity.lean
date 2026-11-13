/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
public import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Dense inclusions between whole-space Sobolev orders

Smooth compactly supported functions belong to every finite Sobolev order.
Their graph-norm density therefore makes each order restriction have dense range.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory
open scoped ENNReal Topology

variable {n k m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set ℝ^n}

/-- Order restriction preserves the bundle of a smooth compactly supported function. -/
theorem lowerOrderCLM_mkWkpSpaceOnOfContDiff (hkm : k ≤ m)
    (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    lowerOrderCLM (Ω := Ω) (p := p) hkm (mkWkpSpaceOnOfContDiff f hf hc) =
      mkWkpSpaceOnOfContDiff f hf hc := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  rw [lowerOrderCLM_apply]
  apply Lp.ext
  exact (mkWkpSpaceOnOfContDiff_apply_ae f hf hc (a.castOrder hkm)).trans
    (mkWkpSpaceOnOfContDiff_apply_ae f hf hc a).symm

/-- On the whole space, increasing finite Sobolev regularity gives a dense subspace. -/
theorem denseRange_lowerOrderCLM (hkm : k ≤ m) (hp : p ≠ ∞) :
    DenseRange (lowerOrderCLM (n := n) (Ω := Set.univ) (p := p) hkm) := by
  intro U
  obtain ⟨f, hf, hc, hlim⟩ := globalApproximation_WkpSpace
    (Approximation.standardMollifier n) hp k U
  rw [← tendsto_iff_norm_sub_tendsto_zero] at hlim
  apply isClosed_closure.mem_of_tendsto hlim
  exact Eventually.of_forall fun j ↦ subset_closure
    ⟨mkWkpSpaceOnOfContDiff (k := m) (f j) (hf j) (hc j),
      lowerOrderCLM_mkWkpSpaceOnOfContDiff hkm (f j) (hf j) (hc j)⟩

/-- On an open domain, forgetting higher derivatives is injective. -/
theorem lowerOrderCLM_injective (hkm : k ≤ m) (hΩ : IsOpen Ω) :
    Function.Injective (lowerOrderCLM (n := n) (Ω := Ω) (p := p) hkm) := by
  intro U V h
  apply wkpBaseCoordinateCLM_injective hΩ
  exact congrArg (wkpBaseCoordinateCLM (m := k)) h

end SobolevSpace.GraphSpace
