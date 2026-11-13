/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.FiniteSums
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Norm decompositions for first-order Sobolev graph spaces

The ambient space `WkpAmbientOn n 1 2 Ω` of a first-order `L²` graph space is the
`PiLp 2` product of one copy of `L²(Ω)` per derivative index, and `DerivIndex n 1`
consists of the base index together with the `n` single-derivative indices
`singleDerivIndex i`.  The `PiLp` norm is therefore the Hilbert-space sum

`‖U‖² = ‖U₀‖²_{L²} + ∑ᵢ ‖Uᵢ‖²_{L²}`,

which is the usual `W^{1,2}` norm `‖u‖² + ‖∇u‖²` once `U` is the derivative tuple
of `u`.  We make the decomposition explicit, together with the matching
one for the inner product. Both use the shared first-order index sum from
`GraphSpace.FiniteSums`. For arbitrary `1 ≤ p ≤ ∞`, the graph norm is at most
the sum of the base and derivative coordinate norms.

## Main results

* `SobolevSpace.GraphSpace.ambient_norm_sq_eq_base_sq_add_sum_deriv_sq`: the
  squared norm splits into base and derivative coordinates.
* `SobolevSpace.GraphSpace.base_norm_sq_add_single_norm_sq_le`: the base together
  with any one derivative coordinate is dominated by the full norm.
* `SobolevSpace.GraphSpace.ambient_inner_eq_base_add_sum_deriv`: the same
  decomposition for the inner product.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The first-order graph norm is at most the sum of its base and derivative
coordinate norms, at any finite or infinite Sobolev exponent. -/
theorem ambient_norm_le_base_add_sum_deriv {n : ℕ} {Ω : Set (ℝ^n)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (U : WkpAmbientOn n 1 p Ω) :
    ‖U‖ ≤ ‖U (baseIndex n 1)‖ + ∑ i : Fin n, ‖U (singleDerivIndex n i)‖ := by
  simpa only [sum_derivIndex_one] using PiLp.norm_le_sum_norm U


/-- Coordinate decomposition of the squared norm in the ambient first-order
Sobolev product space. -/
theorem ambient_norm_sq_eq_base_sq_add_sum_deriv_sq
    (U : WkpAmbientOn n 1 2 Ω) :
    ‖U‖ ^ 2 =
      ‖U (baseIndex n 1)‖ ^ 2 +
        ∑ i : Fin n, ‖U (singleDerivIndex (n := n) i)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, sum_derivIndex_one]

/-- The base coordinate and any one first-derivative coordinate contribute at
most the full squared first-order graph-space norm. -/
theorem base_norm_sq_add_single_norm_sq_le
    (U : WkpAmbientOn n 1 2 Ω) (i : Fin n) :
    ‖U (baseIndex n 1)‖ ^ 2 +
        ‖U (singleDerivIndex (n := n) i)‖ ^ 2 ≤
      ‖U‖ ^ 2 := by
  rw [ambient_norm_sq_eq_base_sq_add_sum_deriv_sq]
  simpa [add_comm] using
    add_le_add_left
      (Finset.single_le_sum (fun j _ ↦ sq_nonneg
        ‖U (singleDerivIndex (n := n) j)‖) (Finset.mem_univ i))
      (‖U (baseIndex n 1)‖ ^ 2)

/-- Coordinate decomposition of the ambient first-order Sobolev inner product. -/
theorem ambient_inner_eq_base_add_sum_deriv
    (U W : WkpAmbientOn n 1 2 Ω) :
    inner ℝ U W =
      inner ℝ (U (baseIndex n 1)) (W (baseIndex n 1)) +
        ∑ i : Fin n,
          inner ℝ (U (singleDerivIndex (n := n) i))
            (W (singleDerivIndex (n := n) i)) := by
  rw [PiLp.inner_apply, sum_derivIndex_one]

end SobolevSpace.GraphSpace
