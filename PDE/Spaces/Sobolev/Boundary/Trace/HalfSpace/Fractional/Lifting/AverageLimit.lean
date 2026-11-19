/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.HeightAverage.Limit
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.LpBound

/-!
# Recovery of boundary data by averaging the mollified extension

The height averages of the cutoff mollified extension converge to its boundary
datum in every finite Lp space with `p ≥ 1`. Slice convergence gives the limit,
and the extension's Lp bound supplies the integrability needed for averaging.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory Filter SobolevSpace.Approximation
open scoped ENNReal Topology

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- The literal height-average errors of the mollified extension tend to zero
in every finite Lp space. -/
theorem tendsto_eLpNorm_heightAverage_mollifiedExtension_sub
    (μ : Mollifier n) (p : ℝ) (hp : 1 ≤ p)
    {g : ℝ^n → F} (hg : MemLp g (ENNReal.ofReal p) volume) :
    Tendsto (fun ε : ℝ ↦ eLpNorm
      (fun x ↦ heightAverage ε (mollifiedExtension μ g) x - g x)
      (ENNReal.ofReal p) volume) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  exact tendsto_eLpNorm_heightAverage_sub p hp
    (memLp_mollifiedExtension μ ENNReal.ofReal_ne_top hg) hg
    (tendsto_eLpNorm_mollifiedExtension_sub μ ENNReal.ofReal_ne_top hg)

/-- Applying the bounded height-average operator to the mollified
extension recovers the boundary Lp class as the positive heights tend to zero. -/
theorem tendsto_heightAverageLp_mollifiedExtension
    (μ : Mollifier n) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p)
    {g : ℝ^n → F} (hg : MemLp g (ENNReal.ofReal p) volume)
    {ι : Type*} {l : Filter ι} (ε : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (hεlim : Tendsto ε l (𝓝[>] (0 : ℝ))) :
    Tendsto (fun i ↦ heightAverageLp n p hp (ε i) (hε i)
      ((memLp_mollifiedExtension μ ENNReal.ofReal_ne_top hg).toLp (mollifiedExtension μ g)))
      l (𝓝 (hg.toLp g)) := by
  exact tendsto_heightAverageLp_of_slice_tendsto p hp
    (memLp_mollifiedExtension μ ENNReal.ofReal_ne_top hg) hg
    (tendsto_eLpNorm_mollifiedExtension_sub μ ENNReal.ofReal_ne_top hg) ε hε hεlim

end SobolevSpace.Trace.HalfSpace
