/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiveDimensional.SourceBounds
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.Amplitude
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.LowEmbedding
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.SpatialSolution
import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.AffineSource

/-!
# Global higher Sobolev persistence in dimension five

The global H² energy evolution and interpolation give affine H³ growth of the
H² source on finite intervals. Restricted Grönwall bounds displacement in H³,
which bounds amplitude in dimension five. Tame composition and Grönwall bound all higher levels.
This is the criterion `higherSmooth_mildLifespan_eq_top_of_affine_source` with the affine
source bound of `exists_norm_higherWaveRestriction_source_affine_bound_five`.
The global second-derivative bound is explicit; higher scalar derivatives
are only bounded on the attained compact value ranges.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {k : ℕ} {f : ℝ → ℝ} {K : ℝ≥0}

/-- In dimension five, smooth globally Lipschitz reactions with bounded second
derivative preserve every sufficiently high Sobolev energy level globally.
Neither amplitude nor any high norm bound is an input. -/
theorem higherSmooth_mildLifespan_eq_top_five (hk : (5 : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0) {D : ℝ} (hD : 0 ≤ D)
    (hsecond : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ D) (x : W^{k + 1,2}(ℝ^5) × W^{k,2}(ℝ^5)) :
    (higherLinearSemigroup 5 k).mildLifespan (higherSmoothMap hk hs hf0) x = ∞ := by
  have hk2 : 2 ≤ k := by
    have : (1 : ℝ) < k := by linarith
    have : 1 < k := by exact_mod_cast this
    omega
  exact higherSmooth_mildLifespan_eq_top_of_affine_source (by norm_num) hk hk2 hs hf hf0
    (fun _ hR ↦ exists_norm_higherWaveRestriction_source_affine_bound_five hk hk2 hs hf hf0 hD
      hsecond hR) x

/-- The original energy solution has a global higher Sobolev lift in dimension
five under the separate global bound on the second reaction derivative. -/
theorem IsEnergySolution.exists_global_higherOrder_smoothReaction_five
    (hk : (5 : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    {D : ℝ} (hD : 0 ≤ D) (hsecond : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ D)
    (x : W^{k + 1,2}(ℝ^5) × W^{k,2}(ℝ^5))
    {e : C(ℝ, H¹(ℝ^5) × DerivLp 5 2 univ)}
    (he : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) e) :
    ∃ U : C(ℝ, W^{k + 1,2}(ℝ^5) × W^{k,2}(ℝ^5)), U 0 = x ∧
      ∀ t : ℝ, 0 ≤ t →
        (lowerOrderCLM (by omega : 1 ≤ k + 1) (U t).1,
          wkpBaseCoordinateCLM (U t).2) = e t := by
  exact he.exists_global_higherOrder_of_mildLifespan_eq_top hk hs hf hf0 x
    (higherSmooth_mildLifespan_eq_top_five hk hs hf hf0 hD hsecond x)

end PDE.Hyperbolic.NonlinearWave.Cauchy
