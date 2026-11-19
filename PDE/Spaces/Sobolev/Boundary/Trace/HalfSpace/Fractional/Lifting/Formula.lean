/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation
public import PDE.Spaces.Sobolev.Boundary.Geometry.TangentialNormal
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.Cutoff

/-!
# Extending boundary data by mollification

At height `t > 0`, smooth the boundary data at scale `t` and multiply by the
height cutoff. The resulting slices approach the data in every finite `Lᵖ`
space with `p ≥ 1`. This is a statement about the slices as the height tends
to zero; the value assigned on the boundary itself is irrelevant.

The formula is defined for data in a real normed space. Sobolev membership
requires a separate estimate for its derivatives.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace SobolevSpace.Trace.HalfSpace

open SobolevSpace.Approximation

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Extend boundary data by mollifying at the current height and cutting off
at height two. The analytic construction uses its restriction to the upper half-space. -/
def mollifiedExtension (μ : Mollifier n) (g : ℝ^n → F) (z : ℝ^(n + 1)) : F :=
  heightCutoff (splitTangentialNormal z).2 •
    mollifyVector μ (splitTangentialNormal z).2 g (splitTangentialNormal z).1

/-- In tangential and normal coordinates, the extension is the mollified
boundary value multiplied by the height cutoff. -/
@[simp] theorem mollifiedExtension_join (μ : Mollifier n) (g : ℝ^n → F)
    (x : ℝ^n) (t : ℝ) :
    mollifiedExtension μ g (joinTangentialNormal (x, t)) =
      heightCutoff t • mollifyVector μ t g x := by
  simp only [mollifiedExtension, split_joinTangentialNormal]

/-- No part of the extension remains above height two. -/
theorem mollifiedExtension_eq_zero_of_two_le_height
    (μ : Mollifier n) (g : ℝ^n → F) (z : ℝ^(n + 1))
    (hz : 2 ≤ (splitTangentialNormal z).2) :
    mollifiedExtension μ g z = 0 := by
  rw [mollifiedExtension, heightCutoff_eq_zero (hz.trans (le_abs_self _)), zero_smul]

/-- The positive-height slices recover the boundary data in `Lᵖ`, for
every finite exponent `p ≥ 1`. -/
theorem tendsto_eLpNorm_mollifiedExtension_sub [CompleteSpace F]
    (μ : Mollifier n) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {g : ℝ^n → F} (hg : MemLp g p volume) :
    Tendsto
      (fun t : ℝ ↦ eLpNorm
        (fun x ↦ mollifiedExtension μ g (joinTangentialNormal (x, t)) - g x) p volume)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  apply (tendsto_eLpNorm_mollifyVector_sub μ hp hg).congr'
  filter_upwards [heightCutoff_eventuallyEq_one.filter_mono nhdsWithin_le_nhds] with t ht
  simp only [mollifiedExtension_join, ht, one_smul]

end SobolevSpace.Trace.HalfSpace
