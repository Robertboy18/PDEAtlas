/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Spectral.RieszProjection.Contour
import PDE.Analysis.Spectral.RieszProjection.PseudoResolvent

/-!
# Idempotence of the Riesz projection and the inverse outside the circle

The resolvent of an element `a` of a complex Banach algebra is a pseudo-resolvent on its
resolvent set, and `rieszIntegral a r g` is the Dunford integral of that pseudo-resolvent on the
circle `C(0, r)` (`rieszIntegral_eq_dunfordIntegral`), so the theorems of
`PDE.Analysis.Spectral.RieszProjection.PseudoResolvent` apply. A circle free of spectrum lies in
an open annulus free of spectrum, and the integrals do not change across such an annulus when
the weight is holomorphic there. For circles of radii `r₁ < r₂` free of spectrum the product
rule reads

`rieszInner a r₁ · Φ_{r₂}(g) = Φ_{r₁}(ĝ)`,   `ĝ(z) = (2πi)⁻¹ ∮_{|w| = r₂} g(w) (w - z)⁻¹ dw`,

and `rieszInner a r` is idempotent (`rieszInner_idem`). With `g(w) = w^{-n}`, `n ≥ 1`, the
transform `ĝ` vanishes on the inner disc.

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

/-- A circle free of spectrum lies in an open annulus free of spectrum. This is
`exists_annulus_subset_of_sphere_subset` for the open resolvent set. -/
theorem exists_annulus_subset_resolventSet {r : ℝ} (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ a) :
    ∃ δ, 0 < δ ∧ δ < r ∧
      ∀ z : ℂ, r - δ < ‖z‖ → ‖z‖ < r + δ → z ∈ resolventSet ℂ a := by
  obtain ⟨δ, hδ, hδr, h⟩ := exists_annulus_subset_of_sphere_subset
    (spectrum.isOpen_resolventSet a) hr (sphere_subset_resolventSet hfree)
  exact ⟨δ, hδ, hδr, fun z h₁ h₂ ↦ h z (by rwa [dist_zero_right]) (by rwa [dist_zero_right])⟩

/-- The weighted integral does not change across a closed annulus free of spectrum on which
the weight is holomorphic. This is `dunfordIntegral_eq_of_annulus` for the resolvent of `a`
and the centre `0`. -/
theorem rieszIntegral_eq_of_annulus {g : ℂ → ℂ} {r₁ r₂ : ℝ} (h₀ : 0 < r₁) (hle : r₁ ≤ r₂)
    (hres : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → z ∈ resolventSet ℂ a)
    (hg : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → DifferentiableAt ℂ g z) :
    rieszIntegral a r₂ g = rieszIntegral a r₁ g := by
  have hmem : ∀ z ∈ closedBall (0 : ℂ) r₂ \ ball 0 r₁, r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ := fun z hz ↦
    ⟨not_lt.mp fun h ↦ hz.2 (mem_ball_zero_iff.mpr h), mem_closedBall_zero_iff.mp hz.1⟩
  exact dunfordIntegral_eq_of_annulus (isPseudoResolventOn_resolvent a)
    (spectrum.isOpen_resolventSet a) h₀ hle
    (fun z hz ↦ hres z (hmem z hz).1 (hmem z hz).2) fun z hz ↦ hg z (hmem z hz).1 (hmem z hz).2

/-- The Riesz projection does not change across a closed annulus free of spectrum. -/
theorem rieszInner_eq_of_annulus {r₁ r₂ : ℝ} (h₀ : 0 < r₁) (hle : r₁ ≤ r₂)
    (hres : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → z ∈ resolventSet ℂ a) :
    rieszInner a r₂ = rieszInner a r₁ := by
  simp only [rieszInner_eq_rieszIntegral]
  exact rieszIntegral_eq_of_annulus h₀ hle hres fun _ _ _ ↦ differentiableAt_const _

/-- The product rule `rieszInner a r₁ · Φ_{r₂}(g) = Φ_{r₁}(ĝ)` for two circles `r₁ < r₂` free
of spectrum, where `ĝ(z) = (2πi)⁻¹ ∮_{|w| = r₂} (w - z)⁻¹ g(w) dw`. This is
`rieszProjection_mul_dunfordIntegral` for the resolvent of `a` and the centre `0`. -/
theorem rieszInner_mul_rieszIntegral {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hs₁ : sphere (0 : ℂ) r₁ ⊆ resolventSet ℂ a) (hs₂ : sphere (0 : ℂ) r₂ ⊆ resolventSet ℂ a)
    {g : ℂ → ℂ} (hg : ContinuousOn g (sphere 0 r₂)) :
    rieszInner a r₁ * rieszIntegral a r₂ g =
      rieszIntegral a r₁ (fun z ↦ (2 * π * I)⁻¹ * ∮ w in C(0, r₂), (w - z)⁻¹ * g w) := by
  rw [rieszInner_eq_rieszProjection]
  exact rieszProjection_mul_dunfordIntegral (isPseudoResolventOn_resolvent a) h₁.le
    (h₁.trans h₁₂).le hs₁ hs₂ (Set.disjoint_left.mpr fun z hz hz' ↦ by
      have h1 := mem_closedBall.mp hz
      have h2 := mem_sphere.mp hz'
      linarith) hg

variable {r : ℝ}

/-- Idempotence for a positive radius: `isIdempotentElem_rieszProjection` for the resolvent of
`a`, which is a pseudo-resolvent on the open resolvent set. -/
private theorem rieszInner_idem_of_pos (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ a) : IsIdempotentElem (rieszInner a r) := by
  rw [rieszInner_eq_rieszProjection]
  exact isIdempotentElem_rieszProjection (isPseudoResolventOn_resolvent a)
    (spectrum.isOpen_resolventSet a) hr (sphere_subset_resolventSet hfree)

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
