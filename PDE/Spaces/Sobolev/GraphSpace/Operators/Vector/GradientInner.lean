/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.FirstOrder
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# The `L²` pairing of weak gradients

For finite systems `u, v` in `W^{1,2}(Ω)^m`, the `L²` inner product of the flattened weak gradients
is the integral of the entrywise products `∑ᵢ ∑ⱼ ∂ⱼuᵢ ∂ⱼvᵢ`.
-/

@[expose] public section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped RealInnerProductSpace Sobolev

variable {m n : ℕ} {Ω : Set (ℝ^n)}

/-- The `L²` inner product of two weak gradients as the integral of the entrywise products. -/
theorem inner_vectorWkpGradientCLM (u v : Fin m → W^{1,2}(Ω)) :
    ⟪∇ u, ∇ v⟫ = ∫ x in Ω, ∑ i, ∑ j,
      ∇ u x (finProdFinEquiv (i, j)) * ∇ v x (finProdFinEquiv (i, j)) := by
  rw [L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [EuclideanSpace.real_inner_eq_sum, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]

end SobolevSpace.GraphSpace
