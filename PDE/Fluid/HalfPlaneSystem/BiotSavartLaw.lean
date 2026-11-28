/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Law
public import PDE.Fluid.Incompressible.HalfPlane.VelocityField
public import PDE.Fluid.Incompressible.HalfPlane.VelocityComparison
import PDE.Analysis.Calculus.FaaDiBrunoBounds

/-!
# The half-plane Biot-Savart law is a velocity law

`isVelocityLaw_halfPlaneVelocity` proves that the half-plane Biot-Savart velocity
`IncompressibleFlow.halfPlaneVelocity`, the velocity of the two-dimensional Boussinesq system,
satisfies `IsVelocityLaw` for data supported in any disc of radius `R₀`, with the constants
`biotSavartConst R₀ k α` collected from the estimates of `IncompressibleFlow`. This gives the class
its first instance.

Each field of `IsVelocityLaw` is one estimate of this library for this velocity: the size of the
velocity of a bounded vorticity with compact support, the Kato bound of its gradient and the
homogeneous form with the Osgood modulus, the vanishing of the normal component on the boundary, the
log-Lipschitz bound of the gradient for a `C¹` vorticity, and the Schauder estimates of order
`k + 1` for a `C^{k,α}` vorticity. The constants of these estimates depend on the support radius
through `R = max R₀ 0`; their sum is a common constant, not optimized, which is all the general
theory needs.

## Main results

* `isVelocityLaw_halfPlaneVelocity`: the half-plane Biot-Savart law is a velocity law with the
  constants `biotSavartConst R₀`, for every radius `R₀`.
* `biotSavartConst`, `biotSavartConst_nonneg`: the constants
  `1 + R² + 200/|α| + 844/|α(1-α)| + 40π(1 + R²) + k + 48 + 4πR²` with `R = max R₀ 0`, and their
  sign.

`isHolderVelocityLaw_halfPlaneVelocity` (`APrioriHolder.lean`) adds the Schauder estimate of the
gradient for Hölder data, and `BoussinesqInstance.lean` combines the two. In BlowupZoo the velocity
near the wall of the cylinder is the planar velocity of a weighted vorticity plus corrections, and
its estimates apply those of the planar law through this theorem.
-/

@[expose] public section

noncomputable section

open Set IncompressibleFlow

open PDE.Analysis (norm_iteratedFDerivWithin_zero_sub)

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The constants of the half-plane Biot-Savart law for data in the disc of radius `R₀`: with
`R = max R₀ 0`, a common bound of the size constant `1 + R²`, the Kato constants `200 / α` and
`32 + 40 π R²`, the Schauder constants `200 / α + 40 π (1 + R²) + k + 33` and
`844 / (α (1 - α)) + k`, and the log-Lipschitz constant `11 + 4 π R² + 4`. -/
def biotSavartConst (R₀ : ℝ) (k : ℕ) (α : ℝ) : ℝ :=
  1 + max R₀ 0 ^ 2 + 200 / |α| + 844 / |α * (1 - α)| + 40 * Real.pi * (1 + max R₀ 0 ^ 2) + k +
    48 + 4 * Real.pi * max R₀ 0 ^ 2

/-- The constants of the half-plane Biot-Savart law are nonnegative. -/
theorem biotSavartConst_nonneg (R₀ : ℝ) (k : ℕ) (α : ℝ) : 0 ≤ biotSavartConst R₀ k α := by
  unfold biotSavartConst; positivity

private theorem support_max {f : ℝ^2 → ℝ} {R : ℝ}
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) :
    ∀ y : ℝ^2, 0 ≤ y 1 → max R 0 < ‖y‖ → f y = 0 :=
  fun y hy h ↦ hR y hy ((le_max_left R 0).trans_lt h)

private theorem max_sq_le {R R₀ : ℝ} (hR : R ≤ R₀) : max R 0 ^ 2 ≤ max R₀ 0 ^ 2 :=
  pow_le_pow_left₀ (le_max_right R 0) (max_le_max hR le_rfl) 2

private theorem fderivWithin_halfPlaneVelocity_zero {x : ℝ^2} :
    fderivWithin ℝ (halfPlaneVelocity (0 : ℝ^2 → ℝ)) H̄ x = 0 := by
  have hG : GreenFunction.halfSpaceGreenPotential (0 : ℝ^2 → ℝ) = fun _ ↦ 0 := by
    funext y
    simp [GreenFunction.halfSpaceGreenPotential]
  have h : halfPlaneVelocity (0 : ℝ^2 → ℝ) = fun _ ↦ 0 := by
    funext y
    ext k
    fin_cases k <;> simp [halfPlaneVelocity, hG, PDE.partialDeriv]
  rw [h]
  exact fderivWithin_const_apply _

/-- **The half-plane Biot-Savart law is a velocity law** for data supported in the disc of radius
`R₀`, with the constants `biotSavartConst R₀`. It is the law of the Boussinesq system;
`BoussinesqInstance.lean` has its coefficient. Proof: each field is an estimate of this library for
the half-plane velocity, and its constant is at most the common constant. -/
theorem isVelocityLaw_halfPlaneVelocity (R₀ : ℝ) :
    IsVelocityLaw halfPlaneVelocity R₀ (biotSavartConst R₀) where
  const_nonneg := biotSavartConst_nonneg R₀
  -- The velocity is a derivative of the Green potential, which depends only on the datum in
  -- the open half-plane.
  congr := by
    intro f g hfg x _
    have h : GreenFunction.halfSpaceGreenPotential f =
        GreenFunction.halfSpaceGreenPotential g :=
      GreenFunction.halfSpaceGreenPotential_congr fun y hy ↦ hfg y (le_of_lt hy)
    simp only [halfPlaneVelocity, h]
  sub := by
    intro f g R _ hf hfR hg hgR x _
    rw [halfPlaneVelocity_sub_of_continuousOn hf hfR hg hgR, Pi.sub_apply]
  -- The size of the velocity of a bounded vorticity with support in a disc.
  norm_le := by
    intro f R B hR hf hfR hB x _
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (by simp))
    refine (norm_halfPlaneVelocity_le_of_abs_le hf (support_max hfR) (le_max_right R 0) hB
      x).trans ?_
    have h1 : 1 + max R 0 ^ 2 ≤ biotSavartConst R₀ 0 0 := by
      have := max_sq_le hR
      unfold biotSavartConst; push_cast; nlinarith [Real.pi_pos, sq_nonneg (max R₀ 0)]
    exact mul_le_mul_of_nonneg_right h1 hB0
  contDiffOn_one := by
    intro f R M α hα hα1 _ hf hfR hM
    have h := IncompressibleFlow.contDiffOn_succ_halfPlaneVelocity hα hα1 (k := 0)
      (by simpa using hf) hfR (M := M) fun y z hy hz ↦ by
        rw [norm_iteratedFDerivWithin_zero_sub, Real.norm_eq_abs]
        exact hM y z hy hz
    simpa using h
  -- The Kato bound of the velocity gradient; its two constants are at most the common one.
  norm_fderivWithin_le := by
    intro f R B M α hα hα1 hR hf hfR hM hM0 hB x hx
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (by simp))
    have h := norm_fderivWithin_halfPlaneVelocity_le_katoBound hf (support_max hfR)
      (le_max_right R 0) hα hα1 hM hB hx
    refine h.trans ?_
    have hlog : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
    have hX : 0 ≤ 1 + B * Real.log (2 + M) := by positivity
    have hsq := max_sq_le hR
    have hα' : |α| = α := abs_of_pos hα
    have hC1 : 200 / α ≤ biotSavartConst R₀ 0 α := by
      unfold biotSavartConst; rw [hα']
      have : 0 ≤ 844 / |α * (1 - α)| := by positivity
      nlinarith [Real.pi_pos, sq_nonneg (max R₀ 0)]
    have hC2 : 32 + 40 * Real.pi * max R 0 ^ 2 ≤ biotSavartConst R₀ 0 α := by
      unfold biotSavartConst
      have : 0 ≤ 844 / |α * (1 - α)| := by positivity
      have : 0 ≤ 200 / |α| := by positivity
      nlinarith [Real.pi_pos, sq_nonneg (max R₀ 0)]
    unfold katoBound
    calc 4 * (50 / α * (1 + B * Real.log (2 + M)) + 8 * B +
          10 * (Real.pi * max R 0 ^ 2 * B))
        = 200 / α * (1 + B * Real.log (2 + M)) + (32 + 40 * Real.pi * max R 0 ^ 2) * B := by
          ring
      _ ≤ biotSavartConst R₀ 0 α * (1 + B * Real.log (2 + M)) +
          biotSavartConst R₀ 0 α * B := by gcongr
      _ = _ := by ring
  -- The homogeneous Kato bound: the comparison of the gradients of two data, with the second
  -- datum zero.
  norm_fderivWithin_le_osgood := by
    intro f R M α η A hα hα1 hR hf hfR hM hM0 hη hηA x hx
    have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη 0 (by simp))
    have h := norm_sub_fderivWithin_halfPlaneVelocity_le (g := 0) hf (support_max hfR)
      continuousOn_const (fun _ _ _ ↦ rfl) (le_max_right R 0) hα hα1 hM
      (Mg := 0) (fun _ _ _ _ ↦ by simp) hM0 le_rfl (fun y hy ↦ by simpa using hη y hy) hηA hx
    rw [fderivWithin_halfPlaneVelocity_zero, sub_zero, add_zero] at h
    refine h.trans ?_
    have hφ : 0 ≤ PDE.Analysis.osgoodModulus (2 * A + M) η := by
      refine le_trans ?_ (PDE.Analysis.mul_one_add_log_le_osgoodModulus hη0 hηA hM0)
      have : 0 ≤ Real.log (2 + M / η) := Real.log_nonneg (by
        have : 0 ≤ M / η := div_nonneg hM0 hη0
        linarith)
      positivity
    have hsq := max_sq_le hR
    have hα' : |α| = α := abs_of_pos hα
    have hC1 : 200 / α ≤ biotSavartConst R₀ 0 α := by
      unfold biotSavartConst; rw [hα']
      have : 0 ≤ 844 / |α * (1 - α)| := by positivity
      nlinarith [Real.pi_pos, sq_nonneg (max R₀ 0)]
    have hC2 : 32 + 40 * Real.pi * max R 0 ^ 2 ≤ biotSavartConst R₀ 0 α := by
      unfold biotSavartConst
      have : 0 ≤ 844 / |α * (1 - α)| := by positivity
      have : 0 ≤ 200 / |α| := by positivity
      nlinarith [Real.pi_pos, sq_nonneg (max R₀ 0)]
    calc 4 * (50 / α * PDE.Analysis.osgoodModulus (2 * A + M) η + 8 * η +
          10 * (Real.pi * max R 0 ^ 2 * η))
        = 200 / α * PDE.Analysis.osgoodModulus (2 * A + M) η +
          (32 + 40 * Real.pi * max R 0 ^ 2) * η := by ring
      _ ≤ biotSavartConst R₀ 0 α * PDE.Analysis.osgoodModulus (2 * A + M) η +
          biotSavartConst R₀ 0 α * η := by gcongr
      _ = _ := by ring
  normal_eq_zero := by
    intro f R _ hf hfR x hx
    exact halfPlaneVelocity_normal_eq_zero hf hfR hx
  -- The log-Lipschitz bound of the velocity gradient of a `C¹` vorticity.
  norm_fderivWithin_sub_le_log := by
    intro f R B₁ hR hf hfR hB y z hy hz
    have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans (hB 0 (by simp))
    have h := dist_fderivWithin_halfPlaneVelocity_le_log_of_support hf (support_max hfR)
      (le_max_right R 0) hB hy hz
    rw [dist_eq_norm] at h
    refine h.trans ?_
    have hsq := max_sq_le hR
    have hC : 11 + 4 * Real.pi * max R 0 ^ 2 + 4 ≤ biotSavartConst R₀ 0 0 := by
      unfold biotSavartConst
      simp only [abs_zero, div_zero, zero_mul, Nat.cast_zero]
      nlinarith [Real.pi_pos, sq_nonneg (max R₀ 0)]
    have hpl : 0 ≤ Real.posLog (1 / ‖y - z‖) := Real.posLog_nonneg
    have hn : 0 ≤ ‖y - z‖ := norm_nonneg _
    calc ‖y - z‖ * (11 * B₁ + 4 * (Real.pi * max R 0 ^ 2 * B₁) +
          4 * B₁ * Real.posLog (1 / ‖y - z‖))
        ≤ ‖y - z‖ * ((11 + 4 * Real.pi * max R 0 ^ 2 + 4) * B₁ *
          (1 + Real.posLog (1 / ‖y - z‖))) := by
          refine mul_le_mul_of_nonneg_left ?_ hn
          nlinarith [Real.pi_pos, sq_nonneg (max R 0), mul_nonneg hB₁ hpl,
            mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg (max R 0))) (mul_nonneg hB₁ hpl)]
      _ ≤ ‖y - z‖ * (biotSavartConst R₀ 0 0 * B₁ * (1 + Real.posLog (1 / ‖y - z‖))) := by
          gcongr
      _ = _ := by ring
  -- The Schauder estimates of order `k + 1` for a `C^{k,α}` vorticity.
  contDiffOn_succ := by
    intro k f R N α _ hα hα1 _ hf hfR _ hM
    exact IncompressibleFlow.contDiffOn_succ_halfPlaneVelocity hα hα1 hf hfR hM
  norm_iteratedFDerivWithin_le := by
    intro k f R N α _ hα hα1 hR hf hfR hN hM j hj x hx
    have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (Nat.zero_le _) 0 (by simp))
    have h := norm_iteratedFDerivWithin_halfPlaneVelocity_le_mul hα hα1 (le_max_right R 0) hf
      (support_max hfR) hN hM hj hx
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hN0)
    have hsq := max_sq_le hR
    unfold biotSavartConst
    rw [abs_of_pos hα]
    have : 0 ≤ 844 / |α * (1 - α)| := by positivity
    nlinarith [Real.pi_pos, sq_nonneg (max R₀ 0)]
  holder_iteratedFDerivWithin := by
    intro k f R N α _ hα hα1 _ hf hfR hN hM x x' hx hx'
    have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (Nat.zero_le _) 0 (by simp))
    have h := norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le hα hα1 hf hfR hM hx hx'
    refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hN0)
      (by positivity))
    have hpos : 0 < α * (1 - α) := mul_pos hα (by linarith)
    unfold biotSavartConst
    rw [abs_of_pos hpos]
    have : 0 ≤ 200 / |α| := by positivity
    nlinarith [Real.pi_pos, sq_nonneg (max R₀ 0)]

end HalfPlaneSystem
