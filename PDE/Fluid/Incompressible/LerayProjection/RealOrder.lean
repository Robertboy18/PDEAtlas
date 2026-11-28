/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection.OrderLowering
public import PDE.Spaces.Sobolev.Fractional.Integer.RealOrders

/-!
# The Leray projection on Sobolev spaces of real order

The Leray projection is bounded on `Hᵏ(ℝⁿ)` for every integer `k ≥ 0`. This module shows that it
is bounded on `H^σ(ℝⁿ)` for every real `σ ≥ 0`, in every dimension, with some constant. The
constant one would follow from the pointwise description of the projection on the Fourier side,
as an orthogonal projection at each frequency, which is not proved here.

## Main results

* `IncompressibleFlow.exists_besselEnergy_leraySobolev_le` (all dimensions, all real `σ ≥ 0`,
  all vector fields in `L²`): `E_σ(Πx) ≤ C E_σ(x)`, where `E_σ` is the Sobolev energy of order
  `σ`.

## How it works

By interpolation. The projection on `L²` has a bounded lift to every `VectorH n k`, namely
`leraySobolev n k`, compatible with lowering the order (`vectorLowerOrderCLM_leraySobolev`), and
an operator with such lifts is bounded on every real order
(`SobolevSpace.Fractional.exists_besselEnergy_le_of_lifts`).
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open scoped ENNReal NNReal Sobolev

namespace IncompressibleFlow

/-- **The Leray projection is bounded on `H^σ` for every real `σ ≥ 0`**: there is `C` with
`E_σ(Πx) ≤ C E_σ(x)` for every vector field `x ∈ L²(ℝⁿ)`, where `E_σ` is the Sobolev energy of
order `σ`. -/
theorem exists_besselEnergy_leraySobolev_le (n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ≥0, ∀ x : VectorH n 0,
      besselEnergy σ (vectorBaseL2 (leraySobolev n 0 x)) ≤ C * besselEnergy σ (vectorBaseL2 x) := by
  simpa using exists_besselEnergy_le_of_lifts (d := 0) (T := fun x ↦ leraySobolev n 0 x)
    (fun x y ↦ map_add _ x y)
    (fun k ↦ ⟨leraySobolev n k, fun u ↦ vectorLowerOrderCLM_leraySobolev (Nat.zero_le k) u⟩) hσ

end IncompressibleFlow
