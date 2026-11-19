/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.Reflection.Ball
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Local reflection comparison from directional decrease

If the derivative in a unit direction is negative at nearby interior points,
reflection across every sufficiently nearby positive-displacement plane strictly
increases the value above that plane. The proof applies the mean value theorem
along the segment joining a point to its reflection.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set Metric Filter
open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Local directional decrease gives reflection comparison, uniformly in the nearby
point and plane displacement. The derivative premise is restricted to the open ball. -/
theorem eventually_lt_reflection_of_eventually_fderiv_neg {u : E → ℝ}
    (hu : Differentiable ℝ u) {e x : E} {a : ℝ} (he : ‖e‖ = 1)
    (ha : 0 < a) (hplane : ⟪x, e⟫ = a)
    (hneg : ∀ᶠ y in 𝓝 x, y ∈ ball (0 : E) 1 → fderiv ℝ u y e < 0) :
    ∀ᶠ p : ℝ × E in 𝓝 (a, x),
      p.2 ∈ ball (0 : E) 1 → p.1 < ⟪p.2, e⟫ →
        u p.2 < u (reflectHyperplane e p.1 p.2) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hneg
  have hleft : ∀ᶠ p : ℝ × E in 𝓝 (a, x), p.2 ∈ ball x r :=
    continuous_snd.continuousAt.eventually (ball_mem_nhds x hr)
  have hR : Tendsto (fun p : ℝ × E ↦ reflectHyperplane e p.1 p.2)
      (𝓝 (a, x)) (𝓝 x) := by
    simpa only [ContinuousAt, reflectHyperplane_eq_self he hplane] using
      (continuous_reflectHyperplane e).continuousAt (x := (a, x))
  filter_upwards [hleft, hR.eventually (ball_mem_nhds x hr),
    continuous_fst.continuousAt.eventually_const_lt ha] with p hpx hRx hpa hp hheight
  let z := reflectHyperplane e p.1 p.2
  have hz : z ∈ ball (0 : E) 1 := by
    have hp' : ‖p.2‖ < 1 := by simpa using hp
    simpa only [mem_ball, dist_zero_right] using
      (norm_reflectHyperplane_le he hpa.le hheight.le).trans_lt hp'
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap z p.2 t ∈ ball (0 : E) 1 ∩ ball x r := by
    exact fun _ ht ↦ ((convex_ball _ _).inter (convex_ball _ _)).lineMap_mem
      ⟨hz, hRx⟩ ⟨hp, hpx⟩ ht
  have hdir : p.2 - z = (2 * (⟪p.2, e⟫ - p.1)) • e := by
    dsimp [z]
    rw [reflectHyperplane_eq he]
    module
  have hg (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ u (AffineMap.lineMap z p.2 s))
        (fderiv ℝ u (AffineMap.lineMap z p.2 t) (p.2 - z)) t :=
    (hu _).hasFDerivAt.comp_hasDerivAt t AffineMap.hasDerivAt_lineMap
  have hanti : StrictAntiOn (fun t : ℝ ↦ u (AffineMap.lineMap z p.2 t)) (Icc 0 1) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t _ ↦ (hg t).continuousAt.continuousWithinAt) (by
        intro t ht
        rw [(hg t).deriv, hdir, map_smul, smul_eq_mul]
        exact mul_neg_of_pos_of_neg (by linarith)
          (hball (hseg t (interior_subset ht)).2 (hseg t (interior_subset ht)).1))
  simpa using hanti (by simp) (by simp) zero_lt_one

end PDE.Analysis
