/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Norms.FirstDerivatives

/-!
# The closed embedding into first derivative graphs

The base L² coordinate and the order-`k` graphs of all first derivatives
give a closed embedding of the order-`k+1` Sobolev graph.
The inverse estimate uses the multi-index norm comparison.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal NNReal Sobolev

variable {n k : ℕ} {Ω : Set ℝ^n}

/-- The base coordinate together with all first derivative graphs. -/
def firstDerivativeGraphCLM :
    W^{k + 1,2}(Ω) →L[ℝ]
      (DerivLp n 2 Ω × (Fin n → W^{k,2}(Ω))) :=
  wkpBaseCoordinateCLM.prod (ContinuousLinearMap.pi fun i ↦
    partialDerivCLM i)

/-- First derivative graphs determine the full graph continuously, even
when the spatial dimension is zero. -/
theorem isClosedEmbedding_firstDerivativeGraphCLM (hΩ : IsOpen Ω) :
    Topology.IsClosedEmbedding (firstDerivativeGraphCLM (n := n) (k := k) (Ω := Ω)) := by
  let J := firstDerivativeGraphCLM (n := n) (k := k) (Ω := Ω)
  let C := succOrderAssemblyNormBound n k
  have hC : 0 ≤ C := by unfold C succOrderAssemblyNormBound; positivity
  let K : ℝ≥0 := ⟨C * (1 + n), by positivity⟩
  have hbound (U : W^{k + 1,2}(Ω)) : ‖U‖ ≤ K * ‖J U‖ := by
    apply (norm_le_base_add_firstDerivatives hΩ U).trans
    change C * (‖(J U).1‖ + ∑ i, ‖(J U).2 i‖) ≤ (C * (1 + n)) * ‖J U‖
    have hs : (∑ i : Fin n, ‖(J U).2 i‖) ≤ (n : ℝ) * ‖J U‖ := by
      calc
        _ ≤ ∑ _i : Fin n, ‖J U‖ :=
          Finset.sum_le_sum fun i _ ↦ (norm_le_pi_norm (J U).2 i).trans (norm_snd_le (J U))
        _ = (n : ℝ) * ‖J U‖ := by simp
    calc
      _ ≤ C * (‖J U‖ + n * ‖J U‖) :=
        mul_le_mul_of_nonneg_left (add_le_add (norm_fst_le (J U)) hs) hC
      _ = _ := by ring
  exact (J.antilipschitz_of_bound hbound).isClosedEmbedding J.uniformContinuous

end SobolevSpace.GraphSpace
