/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Proximal.Energy
public import PDE.Analysis.Convex.Subdifferential.Basic

/-!
# The proximal optimality condition

Minimality along a segment, combined with convexity of the extended energy, bounds the
one-sided increment by a real quadratic polynomial. Passing the segment parameter to zero
produces the supporting inequality for the residual. No derivative of the energy is assumed.

Conversely, the supporting inequality and the exact quadratic expansion give the strong
three-point inequality, with infinite competitors handled in the extended order.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE.Analysis.Convex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Exact increment of the Hilbert quadratic penalty along an affine line. -/
theorem quadraticPenalty_add_smul (lambda : ℝ) (w u d : H) (t : ℝ) :
    quadraticPenalty lambda w (u + t • d) = quadraticPenalty lambda w u +
      t / lambda * inner ℝ (u - w) d + t ^ 2 / (2 * lambda) * ‖d‖ ^ 2 := by
  have hline : u + t • d - w = (u - w) + t • d := by abel
  unfold quadraticPenalty
  rw [hline, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A finite proximal minimizer has the residual as a subgradient. -/
theorem residual_mem_subdifferential_of_minimizes {I : H → EReal} (hproper : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) {lambda : ℝ}
    {w u : H} (hu : I u ≠ ⊤)
    (hmin : ∀ z, proximalEnergy I lambda w u ≤ proximalEnergy I lambda w z) :
    lambda⁻¹ • (w - u) ∈ subdifferential I u := by
  apply (mem_subdifferential_iff hproper).2
  refine ⟨hu, fun z hz ↦ ?_⟩
  have hucoe := EReal.coe_toReal hu (hproper.1 u)
  have hzcoe := EReal.coe_toReal hz (hproper.1 z)
  let C := (I z).toReal - (I u).toReal + inner ℝ (u - w) (z - u) / lambda
  have hsegment (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
      0 ≤ C + t / (2 * lambda) * ‖z - u‖ ^ 2 := by
    have hline : (1 - t) • u + t • z = u + t • (z - u) := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    have henergy := le_of_mem_realEpigraph hconvex hucoe.symm.le hzcoe.symm.le
      (by linarith : 0 ≤ 1 - t) ht.le (by ring : 1 - t + t = 1)
    rw [hline] at henergy
    have hm : (I u).toReal + quadraticPenalty lambda w u ≤
        (1 - t) * (I u).toReal + t * (I z).toReal +
          quadraticPenalty lambda w (u + t • (z - u)) := by
      apply EReal.coe_le_coe_iff.1
      calc
        (((I u).toReal + quadraticPenalty lambda w u : ℝ) : EReal) =
            proximalEnergy I lambda w u := by
          rw [EReal.coe_add, hucoe]
          rfl
        _ ≤ proximalEnergy I lambda w (u + t • (z - u)) := hmin _
        _ ≤ _ := by
          rw [EReal.coe_add]
          exact add_le_add henergy le_rfl
    rw [quadraticPenalty_add_smul] at hm
    have hmul : 0 ≤ t * (C + t / (2 * lambda) * ‖z - u‖ ^ 2) := by
      dsimp [C]
      simp only [div_eq_mul_inv] at hm ⊢
      nlinarith
    exact nonneg_of_mul_nonneg_right hmul ht
  have hlimit : Tendsto (fun t : ℝ ↦ C + t / (2 * lambda) * ‖z - u‖ ^ 2)
      (𝓝[>] 0) (𝓝 C) := by
    have hc : Continuous (fun t : ℝ ↦ C + t / (2 * lambda) * ‖z - u‖ ^ 2) := by
      fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  have hC : 0 ≤ C := by
    apply ge_of_tendsto hlimit
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)]
      with t ht ht1
    exact hsegment t ht ht1
  dsimp [C] at hC
  simp only [real_inner_smul_left, inner_sub_left] at hC ⊢
  simp only [div_eq_mul_inv] at hC
  nlinarith

/-- A supporting residual gives the strong three-point inequality for the extended energy. -/
theorem proximalEnergy_three_point_le {I : H → EReal} (hproper : IsProper I)
    {lambda : ℝ} {w u : H}
    (hsub : lambda⁻¹ • (w - u) ∈ subdifferential I u) (z : H) :
    proximalEnergy I lambda w u + (quadraticPenalty lambda u z : EReal) ≤
      proximalEnergy I lambda w z := by
  obtain ⟨hu, hsupport⟩ := (mem_subdifferential_iff hproper).1 hsub
  by_cases hz : I z = ⊤
  · simp [proximalEnergy, hz]
  have hucoe := EReal.coe_toReal hu (hproper.1 u)
  have hzcoe := EReal.coe_toReal hz (hproper.1 z)
  have hs := hsupport z hz
  have hquad := quadraticPenalty_add_smul lambda w u (z - u) 1
  simp only [one_smul, add_sub_cancel, one_div, one_pow] at hquad
  have hreal : (I u).toReal + quadraticPenalty lambda w u + quadraticPenalty lambda u z ≤
      (I z).toReal + quadraticPenalty lambda w z := by
    simp only [real_inner_smul_left, inner_sub_left] at hs hquad
    dsimp [quadraticPenalty]
    dsimp [quadraticPenalty] at hquad
    simp only [div_eq_mul_inv] at hquad ⊢
    nlinarith
  change I u + _ + _ ≤ I z + _
  rw [← hucoe, ← hzcoe, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
  exact EReal.coe_le_coe_iff.2 hreal

/-- The quadratic minimization condition and the subgradient condition are equivalent. -/
theorem minimizes_proximalEnergy_iff {I : H → EReal} (hproper : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) {lambda : ℝ} (hlambda : 0 < lambda)
    {w u : H} :
    (∀ z, proximalEnergy I lambda w u ≤ proximalEnergy I lambda w z) ↔
      lambda⁻¹ • (w - u) ∈ subdifferential I u := by
  constructor
  · intro hmin
    have hFproper := isProper_proximalEnergy hproper lambda w
    obtain ⟨z, hz⟩ := hFproper.2
    have hFu := ne_top_of_le_ne_top hz (hmin z)
    have hu : I u ≠ ⊤ := by
      intro hu
      apply hFu
      simp [proximalEnergy, hu]
    exact residual_mem_subdifferential_of_minimizes hproper hconvex hu hmin
  · intro hsub z
    have hq : (0 : EReal) ≤ (quadraticPenalty lambda u z : EReal) := by
      apply EReal.coe_nonneg.2
      dsimp [quadraticPenalty]
      positivity
    exact (le_add_of_nonneg_right hq).trans (proximalEnergy_three_point_le hproper hsub z)

end PDE.Analysis.Convex
