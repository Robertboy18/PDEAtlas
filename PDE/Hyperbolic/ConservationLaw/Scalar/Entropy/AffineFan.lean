/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.AffineFan
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy

/-!
# Entropy balances across continuous scalar fans

A smooth middle state satisfying the scalar equation and matching the outer
states has zero entropy production across both fan edges. Compatibility
gives the interior entropy identity; matching states gives both matching
entropy traces. The affine-fan integration theorem then cancels the boundary
terms. Convexity of the entropy is unnecessary for this equality.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Distributions

namespace PDE.Hyperbolic.ConservationLaw.Scalar

/-- Every compatible C¹ entropy pair is conserved by a continuous affine fan
whose smooth middle state satisfies the quasilinear scalar equation. -/
theorem EntropyPair.integral_affineFan_eq_zero {a : ℝ → ℝ} (E : EntropyPair a)
    (φ : 𝓓^{1}(forwardHalfSpace, ℝ)) {sL sR uL uR : ℝ} (hs : sL ≤ sR) {u : ℝ^2 → ℝ}
    (hu : ∀ p ∈ forwardHalfSpace, ContDiffAt ℝ 1 u p)
    (hpde : ∀ p ∈ AffineFan.middleRegion sL sR, (∂[0] u) p + a (u p) * (∂[1] u) p = 0)
    (hL : ∀ t : ℝ, 0 < t → u (AffineInterface.interface sL t) = uL)
    (hR : ∀ t : ℝ, 0 < t → u (AffineInterface.interface sR t) = uR) :
    (∫ p : ℝ^2, AffineFan.profile sL sR (E.η uL) (fun x ↦ E.η (u x)) (E.η uR) p *
      (∂[0] (φ : ℝ^2 → ℝ)) p + AffineFan.profile sL sR (E.q uL) (fun x ↦ E.q (u x)) (E.q uR) p *
      (∂[1] (φ : ℝ^2 → ℝ)) p) = 0 := by
  apply AffineFan.integral_conservative_pair_profile_eq_zero
    φ sL sR hs (fun p ↦ E.η (u p)) (fun p ↦ E.q (u p)) (E.η uL) (E.q uL) (E.η uR) (E.q uR)
    (fun p hp ↦ E.eta_contDiff.contDiffAt.comp p (hu p hp))
    (fun p hp ↦ E.entropyFlux_contDiff.contDiffAt.comp p (hu p hp))
    (fun p hp ↦ entropy_identity_of_pde E ((hu p hp.1).differentiableAt one_ne_zero) (hpde p hp))
  · intro t ht
    rw [hL t ht]
  · intro t ht
    rw [hL t ht]
  · intro t ht
    rw [hR t ht]
  · intro t ht
    rw [hR t ht]

end PDE.Hyperbolic.ConservationLaw.Scalar
