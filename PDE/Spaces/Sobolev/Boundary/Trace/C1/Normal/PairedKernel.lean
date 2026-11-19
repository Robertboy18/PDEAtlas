/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.GradientDifference
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.Separation

/-!
# The paired gradient kernel at a C¹ boundary point

The intrinsic unit normal separates its sufficiently short signed displacements
from every boundary point. The actual fundamental-solution gradient therefore
satisfies the approximate-identity size bound, with one factor of the height.
The radius is selected before the height and integration point. No gradient trace
or separate one-sided limit is assumed.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open Set
open PDE.Analysis PotentialTheory
open scoped Gradient

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
variable [Boundary.C1ExtensionAtlas n Ω]

/-- C¹ boundary geometry gives the size estimate for the actual paired
fundamental-gradient kernel at every boundary point. -/
theorem exists_paired_gradient_fundamentalSolution_bound (hn : 2 ≤ n)
    (x : frontier Ω) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ y ∈ frontier Ω,
      ‖∇ (fundamentalSolution n) ((x : ℝ^n) - t • outwardUnitNormal (Ω := Ω) x - y) -
          ∇ (fundamentalSolution n) ((x : ℝ^n) + t • outwardUnitNormal (Ω := Ω) x - y)‖ ≤
        (2 ^ (n + 1) * ((n : ℝ) + 1) / unitSphereArea n) * t /
          (t + ‖(x : ℝ^n) - y‖) ^ n := by
  obtain ⟨δ, hδ, hsep⟩ := exists_normal_separation (Ω := Ω) x
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ y hy
  apply norm_paired_gradient_fundamentalSolution_le hn (norm_outwardUnitNormal x) ht
  · have h := hsep (-t) (by simpa only [abs_neg, abs_of_pos ht] using htδ) y hy
    simpa only [abs_neg, abs_of_pos ht, neg_smul, ← sub_eq_add_neg, norm_sub_rev y x]
      using h
  · have h := hsep t (by simpa only [abs_of_pos ht] using htδ) y hy
    simpa only [abs_of_pos ht, norm_sub_rev y x] using h

end SobolevSpace.Trace.C1
