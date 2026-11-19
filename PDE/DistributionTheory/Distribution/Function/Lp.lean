/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Distribution
public import PDE.Common.Euclidean
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Domain Lᵖ functions as ordinary distributions

For `p ≥ 1`, an Lᵖ class on an open Euclidean domain defines an ordinary
distribution on that same domain. Bundling the map linearly lets finite sums
and differences of weak derivative coordinates be handled at the quotient
level, with no pointwise choice of representative built into the algebra.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Distributions

namespace Distribution

/-- The linear map from a domain Lᵖ class to its ordinary distribution.
Local integrability follows from `p ≥ 1`; no finite-volume assumption on the
domain is needed. -/
def ofLp {n : ℕ} (Ω : Opens (ℝ^n)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp ℝ p (volume.restrict (Ω : Set (ℝ^n))) →ₗ[ℝ] 𝓓'(Ω, ℝ) where
  toFun f := ofFun Ω f volume ⊤
  map_add' f g := by
    rw [ofFun_congr_ae (Lp.coeFn_add f g)]
    exact ofFun_add
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((Lp.memLp f).locallyIntegrable Fact.out))
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((Lp.memLp g).locallyIntegrable Fact.out))
  map_smul' c f := by
    rw [ofFun_congr_ae (Lp.coeFn_smul c f), ofFun_smul]
    rfl

end Distribution
