/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityField

/-!
# Comparison of the half-plane velocities of two vorticities

For two vorticities `f, g`, continuous on the closed half-plane `H̄`, vanishing there outside the
disc of radius `R`, with `|f - g| ≤ β` on `H̄`, the velocities and their derivatives within `H̄`
differ by amounts controlled by `β`. For the derivatives this is the homogeneous Kato bound of the
difference; the logarithm is absorbed into the Osgood modulus.

For `C¹` vorticity, `norm_fderivWithin_halfPlaneVelocity_sub_le_osgood` writes the log-Lipschitz
bound of `Du` on `H̄` as `‖Du(y) - Du(z)‖ ≤ C φ_A(min ‖y - z‖ A)`, a modulus that is monotone on
`[0, ∞)` (`monotoneOn_osgoodModulus_min`), the form used by the comparison of variations of flows.

## Main results

* `norm_halfPlaneVelocity_sub_le_of_abs_sub_le`: `‖u(f) - u(g)‖ ≤ (1 + R²) β` on the plane.
* `norm_halfPlaneVelocity_le_of_abs_le`: `‖u(f)‖ ≤ (1 + R²) B` for a single vorticity bounded by
  `B`.
* `norm_sub_fderivWithin_halfPlaneVelocity_le`: for `α`-Hölder data and `β ≤ A'`,
  `‖Du(f) - Du(g)‖ ≤ 4((50/α) φ(β) + 8β + 10πR²β)` on `H̄`, with `φ = osgoodModulus (2A' + M)` and
  `M` the sum of the Hölder constants.
* `norm_fderivWithin_halfPlaneVelocity_sub_le_osgood`: for `C¹` vorticity,
  `‖Du(y) - Du(z)‖ ≤ C φ_A(min ‖y - z‖ A)` on `H̄`.
* `monotoneOn_osgoodModulus_min`: the modulus `q ↦ C φ_A(min q A)` is monotone on `[0, ∞)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SobolevSpace

namespace IncompressibleFlow

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {f g : ℝ^2 → ℝ} {R β : ℝ}

/-- The difference of two vorticities vanishing outside a common disc vanishes outside it. -/
theorem sub_eq_zero_of_support (hfR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hgR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → g y = 0) :
    ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → (f - g) y = 0 := fun y hy hyR ↦ by
  simp [hfR y hy hyR, hgR y hy hyR]

/-- **Sup bound of the velocity.** If `|f| ≤ B` on the closed half-plane and `f` vanishes there
outside the disc of radius `R ≥ 0`, then `‖u(f)‖ ≤ (1 + R²) B` everywhere. -/
theorem norm_halfPlaneVelocity_le_of_abs_le {B : ℝ} (hf : ContinuousOn f H̄)
    (hfR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hR0 : 0 ≤ R)
    (hB : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ B) (x : ℝ^2) :
    ‖halfPlaneVelocity f x‖ ≤ (1 + R ^ 2) * B := by
  have hL := setIntegral_upper_le hR0 hf.abs (fun y hy hyR ↦ by simp [hfR y hy hyR])
    (fun y hy ↦ hB y hy) fun y ↦ abs_nonneg _
  have hb := norm_halfPlaneVelocity_le_of_continuousOn hf hfR (B := B)
    (fun y hy ↦ hB y (le_of_lt hy)) x
  have hpi := Real.pi_pos
  calc _ ≤ B + (∫ y in HalfSpace.upper 2, |f y|) / Real.pi := hb
    _ ≤ B + Real.pi * R ^ 2 * B / Real.pi := by gcongr
    _ = (1 + R ^ 2) * B := by field_simp

/-- **Sup bound of the velocity difference.** If `|f - g| ≤ β` on the closed half-plane, then
`‖u(f) - u(g)‖ ≤ (1 + R²) β` everywhere. -/
theorem norm_halfPlaneVelocity_sub_le_of_abs_sub_le (hf : ContinuousOn f H̄)
    (hfR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hg : ContinuousOn g H̄)
    (hgR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → g y = 0) (hR0 : 0 ≤ R)
    (hβ : ∀ y : ℝ^2, 0 ≤ y 1 → |f y - g y| ≤ β) (x : ℝ^2) :
    ‖halfPlaneVelocity f x - halfPlaneVelocity g x‖ ≤ (1 + R ^ 2) * β := by
  have hsub := halfPlaneVelocity_sub_of_continuousOn hf hfR hg hgR
  have hdc : ContinuousOn (f - g) H̄ := hf.sub hg
  have hdR := sub_eq_zero_of_support hfR hgR
  have hL := setIntegral_upper_le hR0 hdc.abs (fun y hy hyR ↦ by simp [hdR y hy hyR])
    (fun y hy ↦ hβ y hy) fun y ↦ abs_nonneg _
  have hb := norm_halfPlaneVelocity_le_of_continuousOn hdc hdR (B := β)
    (fun y hy ↦ hβ y (le_of_lt hy)) x
  rw [hsub, Pi.sub_apply] at hb
  have hpi := Real.pi_pos
  calc _ ≤ β + (∫ y in HalfSpace.upper 2, |(f - g) y|) / Real.pi := hb
    _ ≤ β + Real.pi * R ^ 2 * β / Real.pi := by gcongr
    _ = (1 + R ^ 2) * β := by field_simp

/-- **Homogeneous Kato bound of the difference of the velocity derivatives.** For `α`-Hölder
data with constants `Mf, Mg ≥ 0`, `0 < α < 1`, and `|f - g| ≤ β ≤ A'` on the closed half-plane,
at every point of the closed half-plane
`‖Du(f) - Du(g)‖ ≤ 4((50/α) φ(β) + 8β + 10πR²β)` with `φ = osgoodModulus (2A' + (Mf + Mg))`. -/
theorem norm_sub_fderivWithin_halfPlaneVelocity_le {α Mf Mg A' : ℝ} (hf : ContinuousOn f H̄)
    (hfR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hg : ContinuousOn g H̄)
    (hgR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → g y = 0) (hR0 : 0 ≤ R) (hα : 0 < α) (hα1 : α < 1)
    (hMf : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ Mf * ‖y - z‖ ^ α)
    (hMg : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |g y - g z| ≤ Mg * ‖y - z‖ ^ α)
    (hMf0 : 0 ≤ Mf) (hMg0 : 0 ≤ Mg)
    (hβ : ∀ y : ℝ^2, 0 ≤ y 1 → |f y - g y| ≤ β) (hβA : β ≤ A') {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (halfPlaneVelocity f) H̄ x - fderivWithin ℝ (halfPlaneVelocity g) H̄ x‖ ≤
      4 * (50 / α * PDE.Analysis.osgoodModulus (2 * A' + (Mf + Mg)) β + 8 * β +
        10 * (Real.pi * R ^ 2 * β)) := by
  have hβ0 : 0 ≤ β := (abs_nonneg _).trans (hβ 0 (by simp))
  have hsub := halfPlaneVelocity_sub_of_continuousOn hf hfR hg hgR
  have hdc : ContinuousOn (f - g) H̄ := hf.sub hg
  have hdR := sub_eq_zero_of_support hfR hgR
  have hdM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      |(f - g) y - (f - g) z| ≤ (Mf + Mg) * ‖y - z‖ ^ α := fun y z hy hz ↦ by
    have h1 := hMf y z hy hz
    have h2 := hMg y z hy hz
    simp only [Pi.sub_apply]
    calc |f y - g y - (f z - g z)| = |(f y - f z) - (g y - g z)| := by ring_nf
      _ ≤ |f y - f z| + |g y - g z| := abs_sub _ _
      _ ≤ (Mf + Mg) * ‖y - z‖ ^ α := by linarith
  have hdf := differentiableOn_halfPlaneVelocity hf hfR hα hα1 hMf x hx
  have hdg := differentiableOn_halfPlaneVelocity hg hgR hα hα1 hMg x hx
  rw [← fderivWithin_sub (uniqueDiffOn_closedUpper x hx) hdf hdg, ← hsub]
  have hL := setIntegral_upper_le hR0 hdc.abs (fun y hy hyR ↦ by simp [hdR y hy hyR])
    (fun y hy ↦ hβ y hy) fun y ↦ abs_nonneg _
  rcases hβ0.eq_or_lt with hβz | hβpos
  · subst hβz
    have hzero : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
        |(f - g) y - (f - g) z| ≤ 0 * ‖y - z‖ ^ α := fun y z hy hz ↦ by
      have h1 := hβ y hy
      have h2 := hβ z hz
      simp only [Pi.sub_apply, zero_mul] at h1 h2 ⊢
      have e1 : f y - g y = 0 := abs_nonpos_iff.mp h1
      have e2 : f z - g z = 0 := abs_nonpos_iff.mp h2
      rw [e1, e2, sub_zero, abs_zero]
    have hb := norm_fderivWithin_halfPlaneVelocity_le_holder hdc hdR hα hα1 hzero
      (B := 0) (fun y hy ↦ hβ y hy) hx
    have hL0 : ∫ y in HalfSpace.upper 2, |(f - g) y| ≤ 0 := by simpa using hL
    simp only [PDE.Analysis.osgoodModulus_zero, mul_zero, zero_div, add_zero, zero_add]
      at hb ⊢
    nlinarith
  · have hb := norm_fderivWithin_halfPlaneVelocity_le_kato_homogeneous hdc hdR hα hα1 hdM
      (fun y hy ↦ hβ y hy) hβpos hx
    have hlog := PDE.Analysis.mul_one_add_log_le_osgoodModulus hβ0 hβA (add_nonneg hMf0 hMg0)
    have h50 : 50 * β / α * (1 + Real.log (2 + (Mf + Mg) / β)) =
        50 / α * (β * (1 + Real.log (2 + (Mf + Mg) / β))) := by ring
    rw [h50] at hb
    refine hb.trans ?_
    gcongr

/-- The logarithm `log⁺ (1/q)` is at most `log (A/q)` for `0 < q ≤ A` and `A ≥ 1`. -/
theorem posLog_one_div_le_log {A q : ℝ} (hA : 1 ≤ A) (hq : 0 < q) (hqA : q ≤ A) :
    Real.posLog (1 / q) ≤ Real.log (A / q) := by
  rw [Real.posLog, max_le_iff]
  refine ⟨Real.log_nonneg ((one_le_div hq).mpr hqA), Real.log_le_log (by positivity) ?_⟩
  exact div_le_div_of_nonneg_right hA hq.le

/-- For `A ≥ 1`, `c ≥ 0` and `0 ≤ q ≤ A`, the log-Lipschitz quantity `q (c + 4 log⁺ (1/q))` is at
most `(c + 4) φ_A(q)`. -/
theorem mul_add_posLog_le_osgoodModulus {A c q : ℝ} (hA : 1 ≤ A) (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hqA : q ≤ A) :
    q * (c + 4 * Real.posLog (1 / q)) ≤ (c + 4) * PDE.Analysis.osgoodModulus A q := by
  rcases hq.eq_or_lt with rfl | hq
  · simp
  have hP := posLog_one_div_le_log hA hq hqA
  have hL : 0 ≤ Real.log (A / q) := Real.log_nonneg ((one_le_div hq).mpr hqA)
  unfold PDE.Analysis.osgoodModulus
  have : c + 4 * Real.posLog (1 / q) ≤ (c + 4) * (1 + Real.log (A / q)) := by nlinarith
  calc q * (c + 4 * Real.posLog (1 / q)) ≤ q * ((c + 4) * (1 + Real.log (A / q))) :=
        mul_le_mul_of_nonneg_left this hq.le
    _ = (c + 4) * (q * (1 + Real.log (A / q))) := by ring

/-- The modulus `q ↦ C φ_A(min q A)` is monotone on `[0, ∞)`. -/
theorem monotoneOn_osgoodModulus_min {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C) :
    MonotoneOn (fun q ↦ C * PDE.Analysis.osgoodModulus A (min q A)) (Ici 0) := by
  intro q hq q' hq' hqq'
  have hmq : min q A ∈ Icc 0 A := ⟨le_min hq hA.le, min_le_right _ _⟩
  have hmq' : min q' A ∈ Icc 0 A := ⟨le_min hq' hA.le, min_le_right _ _⟩
  exact mul_le_mul_of_nonneg_left
    (PDE.Analysis.monotoneOn_osgoodModulus hA hmq hmq' (min_le_min_right A hqq')) hC

/-- The modulus `q ↦ C φ_A(min q A)` is nonnegative on `[0, ∞)`. -/
theorem osgoodModulus_min_nonneg {A C q : ℝ} (hA : 0 < A) (hC : 0 ≤ C) (hq : 0 ≤ q) :
    0 ≤ C * PDE.Analysis.osgoodModulus A (min q A) :=
  mul_nonneg hC (PDE.Analysis.osgoodModulus_nonneg (le_min hq hA.le) (min_le_right _ _))

/-- **The log-Lipschitz bound of `Du` as an Osgood modulus.** For `f` `C¹` within the closed
half-plane, vanishing there outside the disc of radius `R ≥ 0`, with gradient within the closed
half-plane bounded by `B₁` and `‖Du(f)‖ ≤ K₁` on the closed half-plane, and `A ≥ 1`, for `y, z` in
the closed half-plane `‖Du(y) - Du(z)‖ ≤ C φ_A(min ‖y - z‖ A)` with
`C = (11 + 4πR² + 4) B₁ + 2K₁/A`. -/
theorem norm_fderivWithin_halfPlaneVelocity_sub_le_osgood {B₁ K₁ A : ℝ}
    (hf : ContDiffOn ℝ 1 f H̄) (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hR0 : 0 ≤ R)
    (hB : ∀ y, 0 ≤ y 1 → ‖fderivWithin ℝ f H̄ y‖ ≤ B₁)
    (hK : ∀ y, 0 ≤ y 1 → ‖fderivWithin ℝ (halfPlaneVelocity f) H̄ y‖ ≤ K₁) (hA : 1 ≤ A)
    {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    ‖fderivWithin ℝ (halfPlaneVelocity f) H̄ y - fderivWithin ℝ (halfPlaneVelocity f) H̄ z‖ ≤
      ((11 + 4 * (Real.pi * R ^ 2) + 4) * B₁ + 2 * K₁ / A) *
        PDE.Analysis.osgoodModulus A (min ‖y - z‖ A) := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans (hB 0 (by simp))
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (hK 0 (by simp))
  have hc : 0 ≤ 11 + 4 * (Real.pi * R ^ 2) := by positivity
  have hφ : 0 ≤ PDE.Analysis.osgoodModulus A (min ‖y - z‖ A) :=
    PDE.Analysis.osgoodModulus_nonneg (le_min (norm_nonneg _) hA0.le) (min_le_right _ _)
  set q := ‖y - z‖ with hqdef
  rcases le_or_gt q A with hqA | hqA
  · rw [min_eq_left hqA]
    have hlog := dist_fderivWithin_halfPlaneVelocity_le_log_of_support hf hR hR0 hB hy hz
    rw [dist_eq_norm] at hlog
    have hm := mul_add_posLog_le_osgoodModulus hA hc (norm_nonneg (y - z)) hqA
    have hφq : 0 ≤ PDE.Analysis.osgoodModulus A q :=
      PDE.Analysis.osgoodModulus_nonneg (norm_nonneg _) hqA
    calc _ ≤ q * (11 * B₁ + 4 * (Real.pi * R ^ 2 * B₁) + 4 * B₁ * Real.posLog (1 / q)) := hlog
      _ = B₁ * (q * (11 + 4 * (Real.pi * R ^ 2) + 4 * Real.posLog (1 / q))) := by ring
      _ ≤ B₁ * ((11 + 4 * (Real.pi * R ^ 2) + 4) * PDE.Analysis.osgoodModulus A q) :=
          mul_le_mul_of_nonneg_left hm hB₁
      _ ≤ _ := by
          have : 0 ≤ 2 * K₁ / A * PDE.Analysis.osgoodModulus A q := by positivity
          nlinarith
  · rw [min_eq_right hqA.le, PDE.Analysis.osgoodModulus_self]
    have h2 : ‖fderivWithin ℝ (halfPlaneVelocity f) H̄ y -
        fderivWithin ℝ (halfPlaneVelocity f) H̄ z‖ ≤ 2 * K₁ :=
      (norm_sub_le _ _).trans (by linarith [hK y hy, hK z hz])
    have hA' : 2 * K₁ / A * A = 2 * K₁ := div_mul_cancel₀ _ hA0.ne'
    have : 0 ≤ (11 + 4 * (Real.pi * R ^ 2) + 4) * B₁ * A := by positivity
    nlinarith

end IncompressibleFlow
