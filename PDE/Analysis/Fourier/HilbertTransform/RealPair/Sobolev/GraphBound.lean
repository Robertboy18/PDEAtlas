/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev.Weak

/-!
# Hilbert bounds from a real H¹ graph

The two graph coordinates control the continuous representative of the
spectral Hilbert transform. The estimate applies directly to the velocity
gradient in a De Gregorio solution.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis SobolevSpace.GraphSpace
open scoped Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- The normalized Hilbert relation gives a pointwise velocity-gradient
bound from the same H¹ graph used to represent the vorticity. -/
theorem norm_hilbertPair_right_le_h1 {c : ℝ → ℝ} (U : W^{1,2}(ℝ^1))
    (hp : IsHilbertPair (realLineRepresentative U) c) (hc : Continuous c) (x : ℝ) :
    ‖c x‖ ≤ 2 * ‖U‖ := by
  have hb := hp.norm_le_eLpNorm_add_weakDerivative hc
    (Lp.memLp (realLineCoordinateCLM (singleDerivIndex 1 0) U))
    (hasWeakTimeDerivativeOn_realLineRepresentative U) x
  rw [← eLpNorm_congr_ae (realLineCoordinate_ae_representative U),
    ← Lp.norm_def, ← Lp.norm_def] at hb
  have h₀ := norm_realLineCoordinateCLM_le (baseIndex 1 1) U
  have h₁ := norm_realLineCoordinateCLM_le (singleDerivIndex 1 0) U
  linarith

end SobolevSpace.GraphSpace
