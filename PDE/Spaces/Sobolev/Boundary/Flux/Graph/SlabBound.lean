/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.Graph.WeightedCollar

/-!
# Linear bounds for compactly weighted graph slabs

The normalized graph-slab limit bounds thin slabs. Integrability of the
compactly supported weight extends the estimate to every positive thickness.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace SobolevSpace.Boundary.Flux.Graph

/-- A nonnegative compact weight has graph-slab integral bounded by a constant
times thickness, uniformly for every positive thickness. -/
theorem exists_pos_integral_linearGraphSlab_le
    {m : ℕ} (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ}
    (hg : Continuous g) {f : ℝ^(m + 1) → ℝ}
    (hf : Continuous f) (hk : HasCompactSupport f) (hpos : ∀ x, 0 ≤ f x) :
    ∃ C > 0, ∀ h > 0,
      (∫ x in {x | linearGraphHeight A g x ∈ Ioo 0 h}, f x) ≤ C * h := by
  let J : ℝ → ℝ := fun h ↦ ∫ x in {x | linearGraphHeight A g x ∈ Ioo 0 h}, f x
  let a : ℝ := |A.symm.toLinearMap.det| *
    ∫ y, f (linearGraphParametrization A g y)
  have ht : Tendsto (fun h ↦ h⁻¹ * J h) (𝓝[>] 0) (𝓝 a) := by
    simpa only [one_mul, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
      using tendsto_normalized_linearGraphSlab_integral A hg hf hk
        (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ)))
  obtain ⟨δ, hδ, hnear⟩ := Metric.mem_nhdsWithin_iff.mp
    (ht.eventually (gt_mem_nhds (lt_add_one a)))
  let I : ℝ := ∫ x, f x
  let C : ℝ := |a| + 1 + |I| / δ
  have hfrac : 0 ≤ |I| / δ := div_nonneg (abs_nonneg _) hδ.le
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun h hh ↦ ?_⟩
  change J h ≤ C * h
  by_cases hsmall : h < δ
  · have hhnear : h ∈ Metric.ball (0 : ℝ) δ ∩ Ioi 0 := by
      refine ⟨?_, hh⟩
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hh]
        using hsmall
    have hJ : h⁻¹ * J h < a + 1 := hnear hhnear
    have hJ' : J h < (a + 1) * h := by
      apply (div_lt_iff₀ hh).mp
      simpa only [div_eq_mul_inv, mul_comm] using hJ
    have haC : a + 1 ≤ C := by dsimp [C]; linarith [le_abs_self a]
    exact hJ'.le.trans (mul_le_mul_of_nonneg_right haC hh.le)
  · have hJ : J h ≤ I :=
      setIntegral_le_integral (hf.integrable_of_hasCompactSupport hk)
        (Eventually.of_forall hpos)
    have hδh : δ ≤ h := le_of_not_gt hsmall
    have hI : |I| ≤ (|I| / δ) * h := by
      have h := mul_le_mul_of_nonneg_left hδh hfrac
      simpa only [div_mul_cancel₀ _ hδ.ne'] using h
    have hfracC : |I| / δ ≤ C := by dsimp [C]; linarith [abs_nonneg a]
    exact hJ.trans ((le_abs_self _).trans (hI.trans
      (mul_le_mul_of_nonneg_right hfracC hh.le)))

end SobolevSpace.Boundary.Flux.Graph
