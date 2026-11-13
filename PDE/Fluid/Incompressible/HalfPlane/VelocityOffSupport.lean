/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.StreamSize
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.HarmonicRegion

/-!
# The half-plane velocity away from the support of the vorticity

For a vorticity `f` continuous on the closed upper half-plane, vanishing there outside the disc
of radius `R` and bounded by `B` there, the stream function `G[f]` (the half-plane Green
potential) satisfies `|G[f](x)| ≤ (1 + R²) B |x|` at every point of the plane
(`abs_halfSpaceGreenPotential_le_mul_norm`), and it is harmonic outside the closed disc of radius
`R`. The interior estimates of harmonic functions bound its derivatives there by its size alone
(`norm_iteratedFDeriv_halfSpaceGreenPotential_le_of_eq_zero_outside`): if `B̄(x, 2r)` lies
outside the disc of radius `R` and inside the closed disc of radius `L`, the derivative of the
velocity `∇^⊥ G[f]` at `x` is at most `8 (1 + R²) B L / r²`
(`norm_fderiv_halfPlaneVelocity_le_of_eq_zero_outside`). No regularity of `f` enters.

## Main results

* `norm_iteratedFDeriv_halfSpaceGreenPotential_le_of_eq_zero_outside`: interior bounds of the
  derivatives of the Green potential outside the support of the source, by its size alone.
* `abs_halfSpaceGreenPotential_le_mul_norm`: `|G[f](x)| ≤ (1 + R²) B |x|` on the plane.
* `norm_fderiv_halfPlaneVelocity_le_of_eq_zero_outside`: if `B̄(x, 2r)` lies outside the disc of
  radius `R` and inside the closed disc of radius `L`, then `‖Du(x)‖ ≤ 8 (1 + R²) B L / r²`.
-/

@[expose] public section

noncomputable section

open Set Metric SobolevSpace

namespace GreenFunction

set_option linter.missingDocs true

/-- **Interior bounds of the Green potential outside the support.** If `Z` is continuous with
compact support and vanishes on the open upper half-plane outside the disc of radius `ρ`, then at
every point `x` with `B̄(x, k r)` outside the closed disc of radius `ρ` the `k`-th derivative of
`G[Z]` is at most `2ᵏ M / rᵏ`, `M` a bound of `|G[Z]|` on `B̄(x, k r)`. -/
theorem norm_iteratedFDeriv_halfSpaceGreenPotential_le_of_eq_zero_outside {Z : ℝ^2 → ℝ}
    (hZ : Continuous Z) (hc : HasCompactSupport Z) {ρ : ℝ}
    (h0 : ∀ y ∈ HalfSpace.upper 2, ρ < ‖y‖ → Z y = 0) (k : ℕ) {x : ℝ^2} {r M : ℝ} (hr : 0 < r)
    (hball : closedBall x ((k : ℝ) * r) ⊆ {y | ρ < ‖y‖})
    (hM : ∀ y ∈ closedBall x ((k : ℝ) * r), |halfSpaceGreenPotential Z y| ≤ M) :
    ‖iteratedFDeriv ℝ k (halfSpaceGreenPotential Z) x‖ ≤ 2 ^ k * M / r ^ k := by
  have hU : IsOpen {y : ℝ^2 | ρ < ‖y‖} := isOpen_lt continuous_const continuous_norm
  have hharm := isHarmonicPDE_halfSpaceGreenPotential_of_eqOn_zero hZ hc hU
    fun _ hy ↦ oddHalfSpaceExtension_eq_zero_outside h0 hy
  simpa using hharm.norm_iteratedFDeriv_le hU hr hball hM

end GreenFunction

namespace IncompressibleFlow

open GreenFunction

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {f : ℝ^2 → ℝ} {R B : ℝ}

/-- **Size of the Green potential on the plane**: `|G[f](x)| ≤ (1 + R²) B |x|`. -/
theorem abs_halfSpaceGreenPotential_le_mul_norm (hf : ContinuousOn f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hR0 : 0 ≤ R)
    (hB : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ B) (x : ℝ^2) :
    |halfSpaceGreenPotential f x| ≤ (1 + R ^ 2) * B * ‖x‖ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (by simp))
  have hc : 0 ≤ (1 + R ^ 2) * B := by positivity
  have h1 : |x 1| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x 1
  by_cases hx : 0 ≤ x 1
  · exact (abs_halfSpaceGreenPotential_le hf hR hR0 hB hx).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans h1) hc)
  · have hlast : (HalfSpace.reflect 2 x) (PDE.Common.lastIndex (n := 2)) =
        -x (PDE.Common.lastIndex (n := 2)) := HalfSpace.reflect_apply_last 2 x
    have hr1 : (HalfSpace.reflect 2 x) 1 = -x 1 := hlast
    have hr : 0 ≤ (HalfSpace.reflect 2 x) 1 := by rw [hr1]; linarith
    have h := abs_halfSpaceGreenPotential_le hf hR hR0 hB hr
    rw [halfSpaceGreenPotential_reflect, abs_neg, hr1] at h
    exact h.trans (mul_le_mul_of_nonneg_left ((neg_le_abs _).trans h1) hc)

/-- **The derivative of the velocity away from the vorticity.** For `f` continuous with compact
support, vanishing on the closed upper half-plane outside the disc of radius `R ≥ 0` and bounded
by `B` there, if `B̄(x, 2r)` lies outside the closed disc of radius `R` and inside the closed disc
of radius `L`, then `|D u(x)| ≤ 8 (1 + R²) B L / r²`. -/
theorem norm_fderiv_halfPlaneVelocity_le_of_eq_zero_outside (hf : Continuous f)
    (hfc : HasCompactSupport f) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hR0 : 0 ≤ R)
    (hB : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ B) {x : ℝ^2} {r L : ℝ} (hr : 0 < r)
    (hball : closedBall x (2 * r) ⊆ {y | R < ‖y‖}) (hL : closedBall x (2 * r) ⊆ closedBall 0 L) :
    ‖fderiv ℝ (halfPlaneVelocity f) x‖ ≤ 8 * ((1 + R ^ 2) * B * L) / r ^ 2 := by
  have h0 : ∀ y ∈ HalfSpace.upper 2, R < ‖y‖ → f y = 0 := fun y hy hyR ↦
    hR y (le_of_lt (show 0 < y 1 from hy)) hyR
  have hx : x ∈ {y : ℝ^2 | R < ‖y‖} := hball (mem_closedBall_self (by positivity))
  have hG : ContDiffAt ℝ (((1 : ℕ) : WithTop ℕ∞) + 1) (halfSpaceGreenPotential f) x :=
    ((contDiffOn_halfSpaceGreenPotential_of_eq_zero_outside hf hfc h0).contDiffAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds hx)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have h := norm_iteratedFDeriv_planarStreamVelocity_le hG
  rw [norm_iteratedFDeriv_one] at h
  have h2 : ((2 : ℕ) : ℝ) * r = 2 * r := by norm_num
  have hM : ∀ y ∈ closedBall x (((2 : ℕ) : ℝ) * r),
      |halfSpaceGreenPotential f y| ≤ (1 + R ^ 2) * B * L := by
    intro y hy
    rw [h2] at hy
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (by simp))
    refine (abs_halfSpaceGreenPotential_le_mul_norm hf.continuousOn hR hR0 hB y).trans ?_
    have hyL : ‖y‖ ≤ L := by simpa using hL hy
    gcongr
  have hD := norm_iteratedFDeriv_halfSpaceGreenPotential_le_of_eq_zero_outside hf hfc h0 2 hr
    (by rwa [h2]) hM
  change ‖fderiv ℝ (planarStreamVelocity (halfSpaceGreenPotential f)) x‖ ≤ _
  calc _ ≤ 2 * ‖iteratedFDeriv ℝ (1 + 1) (halfSpaceGreenPotential f) x‖ := h
    _ ≤ 2 * (2 ^ 2 * ((1 + R ^ 2) * B * L) / r ^ 2) := by gcongr
    _ = 8 * ((1 + R ^ 2) * B * L) / r ^ 2 := by ring

end IncompressibleFlow
