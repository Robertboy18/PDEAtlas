/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Spectral.RieszProjection.Contour

/-!
# Idempotence of the Riesz projection and the inverse outside the circle

For two circles of radii `r₁ < r₂` free of spectrum, the first resolvent identity turns the
product of the Riesz projection on the inner circle with a weighted integral on the outer circle
into one integral on the inner circle:

`rieszInner a r₁ · Φ_{r₂}(g) = Φ_{r₁}(ĝ)`,   `ĝ(z) = (2πi)⁻¹ ∮_{|w| = r₂} g(w) (w - z)⁻¹ dw`.

The remaining double integral is the circle integral of a Cauchy transform, which is
holomorphic in the disc of radius `r₂`, so it vanishes by the Cauchy integral theorem. With
`g = 1` the transform is `1`, and moving the circle across a spectrum-free annulus gives
`rieszInner_idem`. With `g(w) = w^{-n}`, `n ≥ 1`, the transform vanishes.

The element `rieszOuterInverse a r = -(2πi)⁻¹ ∮_{|z| = r} z⁻¹ (z - a)⁻¹ dz` inverts `a` on the
spectral part outside the circle: `a · W = W · a = 1 - P`, `P W = W P = 0`, and
`W^n = -(2πi)⁻¹ ∮_{|z| = r} z^{-n} (z - a)⁻¹ dz` for `n ≥ 1`.
-/

@[expose] public noncomputable section

open Complex Metric Set
open scoped Real

namespace PDE.Analysis.Spectral

/-- The partial-fraction recursion behind `∮_{|w| = R} (w - z)⁻¹ w^{-n} dw = 0`. -/
private theorem sub_inv_mul_inv_pow_succ {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) (hzw : w ≠ z)
    (k : ℕ) :
    (w - z)⁻¹ * (w ^ (k + 1))⁻¹ = z⁻¹ * ((w - z)⁻¹ * (w ^ k)⁻¹ - (w ^ (k + 1))⁻¹) := by
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr hzw
  field_simp
  ring

/-- `∮_{|z| = R} z^{-(n + 2)} dz = 0`. -/
theorem circleIntegral_inv_pow_add_two (R : ℝ) (n : ℕ) :
    (∮ z in C(0, R), (z ^ (n + 2))⁻¹) = 0 := by
  have h := circleIntegral.integral_sub_zpow_of_ne (n := -((n + 2 : ℕ) : ℤ)) (by omega) 0 0 R
  simp only [sub_zero, zpow_neg, zpow_natCast] at h
  exact h

/-- `(2πi)⁻¹ ∮_{|z| = R} z⁻¹ dz = 1` for `R ≠ 0`. -/
theorem two_pi_I_inv_mul_circleIntegral_inv {R : ℝ} (hR : R ≠ 0) :
    (2 * π * I)⁻¹ * (∮ z in C(0, R), z⁻¹) = 1 := by
  have h := circleIntegral.integral_sub_center_inv (0 : ℂ) hR
  simp only [sub_zero] at h
  rw [h, inv_mul_cancel₀ two_pi_I_ne_zero]

/-- For `‖z‖ < R` and `n ≥ 1`, `∮_{|w| = R} (w - z)⁻¹ w^{-n} dw = 0`. At `z = 0` the integrand is
`w^{-(n + 2)}`. -/
theorem circleIntegral_sub_inv_mul_inv_pow {R : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) R)
    (n : ℕ) :
    (∮ w in C(0, R), (w - z)⁻¹ * (w ^ (n + 1))⁻¹) = 0 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp_rw [sub_zero, ← mul_inv, ← pow_succ']
    exact circleIntegral_inv_pow_add_two R n
  have hR : 0 < R := (norm_nonneg z).trans_lt (mem_ball_zero_iff.mp hz)
  have hne : ∀ w ∈ sphere (0 : ℂ) R, w ≠ 0 ∧ w ≠ z := fun w hw ↦ by
    rw [mem_sphere_zero_iff_norm] at hw
    refine ⟨fun h ↦ by simp [h] at hw; linarith, fun h ↦ ?_⟩
    rw [h, ← mem_sphere_zero_iff_norm] at hw
    exact (mem_ball_zero_iff.mp hz).ne (mem_sphere_zero_iff_norm.mp hw)
  have hcont : ∀ k : ℕ, ContinuousOn (fun w : ℂ ↦ (w - z)⁻¹ * (w ^ k)⁻¹) (sphere 0 R) :=
    fun k ↦ ((continuousOn_id.sub continuousOn_const).inv₀ fun w hw ↦
      sub_ne_zero.mpr (hne w hw).2).mul ((continuousOn_id.pow k).inv₀ fun w hw ↦
        pow_ne_zero k (hne w hw).1)
  have hpow : ∀ k : ℕ, ContinuousOn (fun w : ℂ ↦ (w ^ (k + 1))⁻¹) (sphere 0 R) :=
    fun k ↦ (continuousOn_id.pow (k + 1)).inv₀ fun w hw ↦ pow_ne_zero _ (hne w hw).1
  have hstep : ∀ k : ℕ, (∮ w in C(0, R), (w - z)⁻¹ * (w ^ (k + 1))⁻¹) =
      z⁻¹ * ((∮ w in C(0, R), (w - z)⁻¹ * (w ^ k)⁻¹) - ∮ w in C(0, R), (w ^ (k + 1))⁻¹) := by
    intro k
    rw [circleIntegral.integral_congr hR.le fun w hw ↦
      sub_inv_mul_inv_pow_succ hz0 (hne w hw).1 (hne w hw).2 k,
      circleIntegral.integral_const_mul, circleIntegral.integral_sub
        ((hcont k).circleIntegrable hR.le) ((hpow k).circleIntegrable hR.le)]
  have hone : (∮ w in C(0, R), (w ^ (0 + 1))⁻¹) = 2 * π * I := by
    simpa using circleIntegral.integral_sub_center_inv (0 : ℂ) hR.ne'
  induction n with
  | zero =>
    rw [hstep 0, hone]
    simp [circleIntegral.integral_sub_inv_of_mem_ball hz]
  | succ n ih =>
    rw [hstep (n + 1), ih, circleIntegral_inv_pow_add_two R n, sub_zero, mul_zero]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] {a : A}

/-- The product rule `rieszInner a r₁ · Φ_{r₂}(g) = Φ_{r₁}(ĝ)` for two circles `r₁ < r₂` free
of spectrum, where `ĝ(z) = (2πi)⁻¹ ∮_{|w| = r₂} (w - z)⁻¹ g(w) dw`. -/
theorem rieszInner_mul_rieszIntegral {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hs₁ : sphere (0 : ℂ) r₁ ⊆ resolventSet ℂ a) (hs₂ : sphere (0 : ℂ) r₂ ⊆ resolventSet ℂ a)
    {g : ℂ → ℂ} (hg : ContinuousOn g (sphere 0 r₂)) :
    rieszInner a r₁ * rieszIntegral a r₂ g =
      rieszIntegral a r₁ (fun z ↦ (2 * π * I)⁻¹ * ∮ w in C(0, r₂), (w - z)⁻¹ * g w) := by
  set c : ℂ := (2 * π * I)⁻¹ with hc
  have h₂ : 0 < r₂ := h₁.trans h₁₂
  set G : ℂ → A := fun z ↦ ∮ w in C(0, r₂), (w - z)⁻¹ • (g w • resolvent a w) with hGdef
  set h : ℂ → ℂ := fun z ↦ ∮ w in C(0, r₂), (w - z)⁻¹ • g w with hhdef
  have hgR : ContinuousOn (fun w ↦ g w • resolvent a w) (sphere 0 r₂) :=
    continuousOn_smul_resolvent hs₂ hg
  have hnot : ∀ z ∈ ball (0 : ℂ) r₂, z ∉ sphere (0 : ℂ) |r₂| := fun z hz hzs ↦ by
    rw [abs_of_pos h₂, mem_sphere_zero_iff_norm] at hzs
    exact (mem_ball_zero_iff.mp hz).ne hzs
  have hsub : closedBall (0 : ℂ) r₁ ⊆ ball 0 r₂ := closedBall_subset_ball h₁₂
  have hGd : ∀ z ∈ ball (0 : ℂ) r₂, DifferentiableAt ℂ G z := fun z hz ↦
    (hasDerivAt_circleIntegral_sub_inv_smul (hgR.circleIntegrable h₂.le)
      (hnot z hz)).differentiableAt
  have hhd : ∀ z ∈ ball (0 : ℂ) r₂, DifferentiableAt ℂ h z := fun z hz ↦
    (hasDerivAt_circleIntegral_sub_inv_smul (hg.circleIntegrable h₂.le)
      (hnot z hz)).differentiableAt
  have hsph : sphere (0 : ℂ) r₁ ⊆ ball 0 r₂ := sphere_subset_closedBall.trans hsub
  have hG0 : (∮ z in C(0, r₁), G z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable h₁.le countable_empty
      (fun z hz ↦ (hGd z (hsub hz)).continuousAt.continuousWithinAt)
      (fun z hz ↦ hGd z (ball_subset_closedBall.trans hsub hz.1))
  -- the pointwise identity for a point of the inner circle
  have hpt : ∀ z ∈ sphere (0 : ℂ) r₁,
      resolvent a z * rieszIntegral a r₂ g = (c * h z) • resolvent a z - c • G z := by
    intro z hz
    have hzres := hs₁ hz
    have hz₁ : ‖z‖ = r₁ := mem_sphere_zero_iff_norm.mp hz
    have hne : ∀ w ∈ sphere (0 : ℂ) r₂, w ≠ z := fun w hw hwz ↦ by
      rw [mem_sphere_zero_iff_norm, hwz, hz₁] at hw
      exact h₁₂.ne hw
    have hinv : ContinuousOn (fun w : ℂ ↦ (w - z)⁻¹) (sphere 0 r₂) :=
      (continuousOn_id.sub continuousOn_const).inv₀ fun w hw ↦ sub_ne_zero.mpr (hne w hw)
    have hi₁ : CircleIntegrable (fun w ↦ ((w - z)⁻¹ * g w) • resolvent a z) 0 r₂ :=
      ((hinv.mul hg).smul continuousOn_const).circleIntegrable h₂.le
    have hi₂ : CircleIntegrable (fun w ↦ (w - z)⁻¹ • (g w • resolvent a w)) 0 r₂ :=
      (hinv.smul hgR).circleIntegrable h₂.le
    have hl := (ContinuousLinearMap.mul ℂ A (resolvent a z)).map_circleIntegral
      (hgR.circleIntegrable h₂.le)
    simp only [ContinuousLinearMap.mul_apply'] at hl
    unfold rieszIntegral
    rw [mul_smul_comm, hl, circleIntegral.integral_congr h₂.le fun w hw ↦ show
        resolvent a z * (g w • resolvent a w) =
          ((w - z)⁻¹ * g w) • resolvent a z - (w - z)⁻¹ • (g w • resolvent a w) by
        rw [mul_smul_comm, resolvent_mul_resolvent hzres (hs₂ hw) (hne w hw).symm]
        simp only [smul_sub, smul_smul]
        rw [mul_comm (g w)],
      circleIntegral.integral_sub hi₁ hi₂, circleIntegral.integral_smul_const, smul_sub,
      smul_smul]
    rfl
  have hRi : CircleIntegrable (resolvent a) 0 r₁ :=
    (continuousOn_resolvent.mono hs₁).circleIntegrable h₁.le
  have hr := ((ContinuousLinearMap.mul ℂ A).flip (rieszIntegral a r₂ g)).map_circleIntegral hRi
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at hr
  have hhc : ContinuousOn (fun z ↦ (c * h z) • resolvent a z) (sphere 0 r₁) :=
    continuousOn_smul_resolvent hs₁ (continuousOn_const.mul fun z hz ↦
      (hhd z (hsph hz)).continuousAt.continuousWithinAt)
  have hGc : ContinuousOn (fun z ↦ c • G z) (sphere 0 r₁) :=
    continuousOn_const.smul fun z hz ↦ (hGd z (hsph hz)).continuousAt.continuousWithinAt
  have hP : rieszInner a r₁ = c • ∮ z in C(0, r₁), resolvent a z := by
    rw [rieszInner_eq_rieszIntegral]
    unfold rieszIntegral
    simp only [Pi.one_apply, one_smul]
    rfl
  rw [hP, smul_mul_assoc, hr, circleIntegral.integral_congr h₁.le hpt,
    circleIntegral.integral_sub (hhc.circleIntegrable h₁.le) (hGc.circleIntegrable h₁.le),
    circleIntegral.integral_smul, hG0, smul_zero, sub_zero]
  rfl

/-- For circles `r₁ < r₂` free of spectrum,
`rieszInner a r₁ · rieszInner a r₂ = rieszInner a r₁`. -/
theorem rieszInner_mul_rieszInner_of_lt {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hs₁ : sphere (0 : ℂ) r₁ ⊆ resolventSet ℂ a) (hs₂ : sphere (0 : ℂ) r₂ ⊆ resolventSet ℂ a) :
    rieszInner a r₁ * rieszInner a r₂ = rieszInner a r₁ := by
  rw [rieszInner_eq_rieszIntegral a r₂, rieszInner_mul_rieszIntegral (g := 1) h₁ h₁₂ hs₁ hs₂
    continuousOn_const, rieszInner_eq_rieszIntegral a r₁]
  refine rieszIntegral_congr h₁.le fun z hz ↦ ?_
  have hz' : z ∈ ball (0 : ℂ) r₂ := sphere_subset_closedBall.trans (closedBall_subset_ball h₁₂) hz
  simp only [Pi.one_apply, mul_one, circleIntegral.integral_sub_inv_of_mem_ball hz']
  exact inv_mul_cancel₀ (by simp [Real.pi_ne_zero])

variable {r : ℝ}

/-- Idempotence for a positive radius: the projection on the circle of radius `r` equals the
one on a slightly larger circle, and the product rule applies to the two circles. -/
private theorem rieszInner_idem_of_pos (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ a) : IsIdempotentElem (rieszInner a r) := by
  obtain ⟨δ, hδ, -, h⟩ := exists_annulus_subset_resolventSet hr hfree
  have hs := sphere_subset_resolventSet hfree
  have hs₂ := sphere_subset_resolventSet_of_annulus h (ρ := r + δ / 2) (by linarith)
    (by linarith)
  have heq : rieszInner a (r + δ / 2) = rieszInner a r :=
    rieszInner_eq_of_annulus hr (by linarith) fun z h₁ h₂ ↦ h z (by linarith) (by linarith)
  unfold IsIdempotentElem
  calc rieszInner a r * rieszInner a r = rieszInner a r * rieszInner a (r + δ / 2) := by
        rw [heq]
    _ = rieszInner a r := rieszInner_mul_rieszInner_of_lt hr (by linarith) hs hs₂

/-- **Idempotence of the Riesz projection.** If the circle of radius `r` carries no spectrum of
`a`, then `rieszInner a r` is idempotent. For `r ≤ 0` the hypothesis is empty and the
conclusion still holds: `C(0, r)` runs over the circle of radius `|r|`, and the integral over
that circle is either the Riesz projection for the radius `|r|` or `0`. -/
theorem rieszInner_idem (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ a) :
    IsIdempotentElem (rieszInner a r) := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · rw [← neg_neg r, rieszInner_neg_radius]
    by_cases hz : ∃ z : ℂ, ‖z‖ = -r ∧ z ∈ spectrum ℂ a
    · obtain ⟨z, hz, hzσ⟩ := hz
      rw [rieszInner_eq_zero_of_mem_spectrum hz hzσ]
      exact IsIdempotentElem.zero
    · exact rieszInner_idem_of_pos (neg_pos.mpr hr) fun z hz' hzσ ↦ hz ⟨z, hz', hzσ⟩
  · simp [IsIdempotentElem, rieszInner]
  · exact rieszInner_idem_of_pos hr hfree

/-- For circles `r₁ < r₂` free of spectrum and `n ≥ 1`,
`rieszInner a r₁ · (2πi)⁻¹ ∮_{|z| = r₂} z^{-n} (z - a)⁻¹ dz = 0`. -/
theorem rieszInner_mul_rieszIntegral_inv_pow {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hs₁ : sphere (0 : ℂ) r₁ ⊆ resolventSet ℂ a) (hs₂ : sphere (0 : ℂ) r₂ ⊆ resolventSet ℂ a)
    (n : ℕ) : rieszInner a r₁ * rieszIntegral a r₂ (fun z ↦ (z ^ (n + 1))⁻¹) = 0 := by
  have hcont : ContinuousOn (fun z : ℂ ↦ (z ^ (n + 1))⁻¹) (sphere 0 r₂) :=
    (continuousOn_id.pow (n + 1)).inv₀ fun z hz ↦
      pow_ne_zero _ (ne_zero_of_mem_sphere (h₁.trans h₁₂).ne' ⟨z, hz⟩)
  rw [rieszInner_mul_rieszIntegral h₁ h₁₂ hs₁ hs₂ hcont, ← rieszIntegral_zero a r₁]
  refine rieszIntegral_congr h₁.le fun z hz ↦ ?_
  have hz' : z ∈ ball (0 : ℂ) r₂ := sphere_subset_closedBall.trans (closedBall_subset_ball h₁₂) hz
  simp only [Pi.zero_apply]
  rw [circleIntegral_sub_inv_mul_inv_pow hz' n, mul_zero]

/-- The weighted integrals with weights `z^{-n}`, `n ≥ 1`, do not change across a
spectrum-free annulus. -/
theorem rieszIntegral_inv_pow_eq_of_annulus {r₁ r₂ : ℝ} (h₀ : 0 < r₁) (hle : r₁ ≤ r₂)
    (hres : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → z ∈ resolventSet ℂ a) (n : ℕ) :
    rieszIntegral a r₂ (fun z ↦ (z ^ n)⁻¹) = rieszIntegral a r₁ (fun z ↦ (z ^ n)⁻¹) :=
  rieszIntegral_eq_of_annulus h₀ hle hres fun _ h₁ _ ↦ (differentiableAt_pow n).inv
    (pow_ne_zero n (norm_pos_iff.mp (h₀.trans_le h₁)))

/-- If the circle of radius `r > 0` carries no spectrum, the Riesz projection annihilates the
integrals with weights `z^{-n}`, `n ≥ 1`, on the same circle. -/
theorem rieszInner_mul_rieszIntegral_inv_pow_self (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ a) (n : ℕ) :
    rieszInner a r * rieszIntegral a r (fun z ↦ (z ^ (n + 1))⁻¹) = 0 := by
  obtain ⟨δ, hδ, -, h⟩ := exists_annulus_subset_resolventSet hr hfree
  have hs := sphere_subset_resolventSet hfree
  have hs₂ := sphere_subset_resolventSet_of_annulus h (ρ := r + δ / 2) (by linarith)
    (by linarith)
  rw [← rieszIntegral_inv_pow_eq_of_annulus hr (r₂ := r + δ / 2) (by linarith)
    (fun z h₁ h₂ ↦ h z (by linarith) (by linarith)) (n + 1)]
  exact rieszInner_mul_rieszIntegral_inv_pow hr (by linarith) hs hs₂ n

omit [CompleteSpace A] in
/-- The inverse of `a` on its spectral part outside the circle of radius `r`,
`-(2πi)⁻¹ ∮_{|z| = r} z⁻¹ (z - a)⁻¹ dz`. -/
def rieszOuterInverse (a : A) (r : ℝ) : A := -rieszIntegral a r fun z ↦ z⁻¹

/-- An element commuting with `a` commutes with the outer inverse. -/
theorem commute_rieszOuterInverse {b : A} (h : Commute b a) (r : ℝ) :
    Commute b (rieszOuterInverse a r) :=
  (commute_rieszIntegral h r _).neg_right

/-- On a circle free of spectrum, `a · rieszOuterInverse a r = 1 - rieszInner a r`. -/
theorem mul_rieszOuterInverse (hr : 0 < r) (hres : sphere (0 : ℂ) r ⊆ resolventSet ℂ a) :
    a * rieszOuterInverse a r = 1 - rieszInner a r := by
  have hinv : ContinuousOn (fun z : ℂ ↦ z⁻¹) (sphere 0 r) :=
    continuousOn_inv₀.mono fun z hz ↦ ne_zero_of_mem_sphere hr.ne' ⟨z, hz⟩
  have h1 : rieszIntegral a r (fun z ↦ z * z⁻¹) = rieszIntegral a r 1 :=
    rieszIntegral_congr hr.le fun z hz ↦ mul_inv_cancel₀ (ne_zero_of_mem_sphere hr.ne' ⟨z, hz⟩)
  unfold rieszOuterInverse
  rw [mul_neg, mul_rieszIntegral hr.le hres hinv, rieszInner_eq_rieszIntegral, h1,
    two_pi_I_inv_mul_circleIntegral_inv hr.ne', one_smul, neg_sub]

/-- On a circle free of spectrum, `rieszOuterInverse a r · a = 1 - rieszInner a r`. -/
theorem rieszOuterInverse_mul (hr : 0 < r) (hres : sphere (0 : ℂ) r ⊆ resolventSet ℂ a) :
    rieszOuterInverse a r * a = 1 - rieszInner a r := by
  rw [← (commute_rieszOuterInverse (Commute.refl a) r).eq, mul_rieszOuterInverse hr hres]

/-- The Riesz projection annihilates the outer inverse. -/
theorem rieszInner_mul_rieszOuterInverse (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ a) :
    rieszInner a r * rieszOuterInverse a r = 0 := by
  have h := rieszInner_mul_rieszIntegral_inv_pow_self hr hfree 0
  simp only [zero_add, pow_one] at h
  rw [rieszOuterInverse, mul_neg, h, neg_zero]

/-- The outer inverse annihilates the Riesz projection. -/
theorem rieszOuterInverse_mul_rieszInner (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ a) :
    rieszOuterInverse a r * rieszInner a r = 0 := by
  rw [(commute_rieszInner (commute_rieszOuterInverse (Commute.refl a) r).symm).eq,
    rieszInner_mul_rieszOuterInverse hr hfree]

/-- The powers of the outer inverse are the integrals with weights `z^{-n}`:
`W^(n+1) = -(2πi)⁻¹ ∮_{|z| = r} z^{-(n+1)} (z - a)⁻¹ dz`. -/
theorem rieszOuterInverse_pow_succ (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ a) (n : ℕ) :
    rieszOuterInverse a r ^ (n + 1) = -rieszIntegral a r (fun z ↦ (z ^ (n + 1))⁻¹) := by
  have hres := sphere_subset_resolventSet hfree
  set W := rieszOuterInverse a r
  set P := rieszInner a r
  set V : ℕ → A := fun k ↦ -rieszIntegral a r (fun z ↦ (z ^ (k + 1))⁻¹) with hV
  have hne : ∀ z ∈ sphere (0 : ℂ) r, z ≠ 0 := fun z hz ↦ ne_zero_of_mem_sphere hr.ne' ⟨z, hz⟩
  have hPV : ∀ k, P * V k = 0 := fun k ↦ by
    simp only [hV, mul_neg, rieszInner_mul_rieszIntegral_inv_pow_self hr hfree k, neg_zero, P]
  have haV : ∀ k, a * V (k + 1) = V k := fun k ↦ by
    have hcont : ContinuousOn (fun z : ℂ ↦ (z ^ (k + 1 + 1))⁻¹) (sphere 0 r) :=
      (continuousOn_id.pow _).inv₀ fun z hz ↦ pow_ne_zero _ (hne z hz)
    simp only [hV, mul_neg]
    rw [mul_rieszIntegral hr.le hres hcont, circleIntegral_inv_pow_add_two r k, mul_zero,
      zero_smul, sub_zero]
    congr 1
    refine rieszIntegral_congr hr.le fun z hz ↦ ?_
    have := hne z hz
    field_simp
    ring
  have hW : W = V 0 := by
    simp only [W, rieszOuterInverse, hV, zero_add, pow_one]
  have hPW : P * W = 0 := rieszInner_mul_rieszOuterInverse hr hfree
  have haW : a * W = 1 - P := mul_rieszOuterInverse hr hres
  have hWa : W * a = 1 - P := rieszOuterInverse_mul hr hres
  induction n with
  | zero => rw [zero_add, pow_one, hW]
  | succ n ih =>
    change W ^ (n + 1 + 1) = V (n + 1)
    rw [pow_succ', ih]
    change W * V n = V (n + 1)
    have haD : a * (V (n + 1) - W * V n) = 0 := by
      rw [mul_sub, haV, ← mul_assoc, haW, sub_mul, one_mul, hPV, sub_zero, sub_self]
    have hPD : P * (V (n + 1) - W * V n) = 0 := by
      rw [mul_sub, hPV, ← mul_assoc, hPW, zero_mul, sub_zero]
    have hD : V (n + 1) - W * V n = 0 := by
      calc V (n + 1) - W * V n = ((1 - P) + P) * (V (n + 1) - W * V n) := by
            rw [sub_add_cancel, one_mul]
        _ = W * (a * (V (n + 1) - W * V n)) + P * (V (n + 1) - W * V n) := by
            rw [add_mul, ← hWa, mul_assoc]
        _ = 0 := by rw [haD, hPD, mul_zero, add_zero]
    exact (sub_eq_zero.mp hD).symm

end PDE.Analysis.Spectral
