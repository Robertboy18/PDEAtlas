/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FourDimensional.GlobalHigher

/-!
# Global classical correspondence in dimension four

The derived global higher lift and the integrated energy equations supply
both time derivatives. Sobolev embedding supplies the spatial and mixed
derivatives. The resulting jointly C² function represents the original
energy evolution at every nonnegative time.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Laplacian Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {k : ℕ} {f : ℝ → ℝ} {K : ℝ≥0}

/-- In dimension four, the original energy evolution from sufficiently high
Sobolev data admits a global jointly C² representative when the smooth globally
Lipschitz reaction has bounded second derivative. All regularity is derived. -/
theorem IsEnergySolution.exists_global_pointwise_smoothReaction_four
    (hk : (4 : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    {D : ℝ} (hD : 0 ≤ D) (hsecond : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ D)
    (hq : (4 : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hv : (4 : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (x : W^{k + 2,2}(ℝ^4) × W^{k + 1,2}(ℝ^4))
    {e : C(ℝ, H¹(ℝ^4) × DerivLp 4 2 univ)}
    (he : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 2) x.1, wkpBaseCoordinateCLM x.2) e) :
    ∃ q v a : C(ℝ × ℝ^4, ℝ),
      ContDiffOn ℝ 2 q (Ioi 0 ×ˢ univ) ∧
      (∀ y, q (0, y) = classicalRepresentativeCLM hq x.1 y ∧
        v (0, y) = classicalRepresentativeCLM hv x.2 y) ∧
      ∀ t : ℝ, 0 ≤ t →
        (fun y ↦ q (t, y)) =ᵐ[volume] baseRepresentative (e t).1 ∧
        (fun y ↦ v (t, y)) =ᵐ[volume] (e t).2 ∧
        ContDiff ℝ 2 (fun y ↦ q (t, y)) ∧
        ∀ y, HasDerivWithinAt (fun s ↦ q (s, y)) (v (t, y)) (Ici 0) t ∧
          HasDerivWithinAt (fun s ↦ v (s, y)) (a (t, y)) (Ici 0) t ∧
          a (t, y) - Δ (fun z ↦ q (t, z)) y + f (q (t, y)) = 0 := by
  obtain ⟨U, hU₀, hU⟩ :=
    he.exists_global_higherOrder_smoothReaction_four hv hs hf hf0 hD hsecond x
  exact he.exists_global_pointwise_higherLift_smoothReaction hk hs hf hf0 hq hv x U hU₀ hU

end PDE.Hyperbolic.NonlinearWave.Cauchy
