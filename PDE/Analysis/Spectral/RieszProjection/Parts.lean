/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Spectral.RieszProjection.Idempotent

/-!
# The spectral parts inside and outside a circle

Let the circle of radius `r > 0` carry no spectrum of `a`, and let `P = rieszInner a r`.
Moving the circle inward or outward across a spectrum-free annulus gives the quantitative
statements of the Riesz decomposition:

* the inner part decays geometrically below `r`: `‖a^n P‖ ≤ C ρ^n` for some `ρ < r`;
* the outer inverse `W = rieszOuterInverse a r` satisfies `‖W^n (1 - P)‖ ≤ C ρ^{-n}` for some
  `ρ > r`;
* for `‖μ‖ ≥ r`, the element `μ - a` is invertible in the corner `P A P`, and for `‖μ‖ ≤ r`
  in the corner `(1 - P) A (1 - P)`.
-/

@[expose] public noncomputable section

open Complex Metric Set
open scoped Real

namespace PDE.Analysis.Spectral

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] {a : A} {r : ℝ}

/-- **Power bound on the inner part.** If the circle of radius `r > 0` carries no spectrum,
then `‖a^n · rieszInner a r‖ ≤ C ρ^n` for some `0 < ρ < r`. -/
theorem exists_norm_pow_mul_rieszInner_le (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ a) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ < r ∧ 0 ≤ C ∧ ∀ n : ℕ, ‖a ^ n * rieszInner a r‖ ≤ C * ρ ^ n := by
  obtain ⟨δ, hδ, hδr, h⟩ := exists_annulus_subset_resolventSet hr hfree
  have hρ : 0 < r - δ / 2 := by linarith
  have hsρ := sphere_subset_resolventSet_of_annulus h (ρ := r - δ / 2) (by linarith)
    (by linarith)
  obtain ⟨M, hM0, hM⟩ := exists_norm_resolvent_le hsρ
  have heq : rieszInner a r = rieszInner a (r - δ / 2) :=
    rieszInner_eq_of_annulus hρ (by linarith) fun z h₁ h₂ ↦ h z (by linarith) (by linarith)
  refine ⟨r - δ / 2, (r - δ / 2) * M, hρ, by linarith, by positivity, fun n ↦ ?_⟩
  rw [heq, pow_mul_rieszInner hρ.le hsρ n]
  calc ‖rieszIntegral a (r - δ / 2) (fun z ↦ z ^ n)‖
      ≤ (r - δ / 2) * ((r - δ / 2) ^ n * M) := norm_rieszIntegral_le hρ.le fun z hz ↦ by
        rw [norm_smul, norm_pow, mem_sphere_zero_iff_norm.mp hz]
        exact mul_le_mul_of_nonneg_left (hM z hz) (by positivity)
    _ = (r - δ / 2) * M * (r - δ / 2) ^ n := by ring

/-- **Inverse bound on the outer part.** If the circle of radius `r > 0` carries no spectrum,
then `‖W^n (1 - rieszInner a r)‖ ≤ C ρ^{-n}` for the outer inverse `W` and some `ρ > r`. -/
theorem exists_norm_rieszOuterInverse_pow_mul_le (hr : 0 < r)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ a) :
    ∃ ρ C : ℝ, r < ρ ∧ 0 ≤ C ∧ ∀ n : ℕ,
      ‖rieszOuterInverse a r ^ n * (1 - rieszInner a r)‖ ≤ C * (ρ ^ n)⁻¹ := by
  obtain ⟨δ, hδ, -, h⟩ := exists_annulus_subset_resolventSet hr hfree
  have hρ : 0 < r + δ / 2 := by linarith
  have hsρ := sphere_subset_resolventSet_of_annulus h (ρ := r + δ / 2) (by linarith)
    (by linarith)
  obtain ⟨M, hM0, hM⟩ := exists_norm_resolvent_le hsρ
  refine ⟨r + δ / 2, max ((r + δ / 2) * M) ‖1 - rieszInner a r‖, by linarith,
    le_max_of_le_left (by positivity), fun n ↦ ?_⟩
  cases n with
  | zero => simp
  | succ n =>
    have hWP : rieszOuterInverse a r ^ (n + 1) * rieszInner a r = 0 := by
      rw [pow_succ, mul_assoc, rieszOuterInverse_mul_rieszInner hr hfree, mul_zero]
    rw [mul_sub, mul_one, hWP, sub_zero, rieszOuterInverse_pow_succ hr hfree n, norm_neg,
      ← rieszIntegral_inv_pow_eq_of_annulus hr (r₂ := r + δ / 2) (by linarith)
        (fun z h₁ h₂ ↦ h z (by linarith) (by linarith))]
    calc ‖rieszIntegral a (r + δ / 2) fun z ↦ (z ^ (n + 1))⁻¹‖
        ≤ (r + δ / 2) * (((r + δ / 2) ^ (n + 1))⁻¹ * M) :=
          norm_rieszIntegral_le hρ.le fun z hz ↦ by
            rw [norm_smul, norm_inv, norm_pow, mem_sphere_zero_iff_norm.mp hz]
            exact mul_le_mul_of_nonneg_left (hM z hz) (by positivity)
      _ = (r + δ / 2) * M * ((r + δ / 2) ^ (n + 1))⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- The resolvent formula along a circle:
`(μ - a) Φ_ρ((μ - z)⁻¹) = rieszInner a ρ + ((2πi)⁻¹ ∮ (μ - z)⁻¹ dz) · 1` for `μ` off the circle. -/
theorem smul_one_sub_mul_rieszIntegral_sub_inv {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hs : sphere (0 : ℂ) ρ ⊆ resolventSet ℂ a) {μ : ℂ} (hμ : ‖μ‖ ≠ ρ) :
    (μ • (1 : A) - a) * rieszIntegral a ρ (fun z ↦ (μ - z)⁻¹) =
      rieszInner a ρ + ((2 * π * I)⁻¹ * ∮ z in C(0, ρ), (μ - z)⁻¹) • (1 : A) := by
  have hne : ∀ z ∈ sphere (0 : ℂ) ρ, μ - z ≠ 0 := fun z hz h ↦
    hμ (by rw [sub_eq_zero.mp h]; exact mem_sphere_zero_iff_norm.mp hz)
  have hcont : ContinuousOn (fun z : ℂ ↦ (μ - z)⁻¹) (sphere 0 ρ) :=
    (continuousOn_const.sub continuousOn_id).inv₀ hne
  have hc1 : ContinuousOn (fun z : ℂ ↦ μ * (μ - z)⁻¹) (sphere 0 ρ) := continuousOn_const.mul hcont
  have hc2 : ContinuousOn (fun z : ℂ ↦ z * (μ - z)⁻¹) (sphere 0 ρ) := continuousOn_id.mul hcont
  have key : μ • rieszIntegral a ρ (fun z ↦ (μ - z)⁻¹) -
      rieszIntegral a ρ (fun z ↦ z * (μ - z)⁻¹) = rieszInner a ρ := by
    rw [← rieszIntegral_smul, ← rieszIntegral_sub hρ hs hc1 hc2, rieszInner_eq_rieszIntegral]
    exact rieszIntegral_congr hρ fun z hz ↦ by
      rw [Pi.one_apply, ← sub_mul, mul_inv_cancel₀ (hne z hz)]
  rw [sub_mul, smul_mul_assoc, one_mul, mul_rieszIntegral hρ hs hcont, ← key]
  abel

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
/-- An invertibility criterion in a corner: if `Q` is idempotent, `x`, `Q` and `b₀` commute,
and `x b₀ = Q`, then `b = Q b₀` inverts `x` in `Q A Q`. -/
theorem exists_corner_inverse {x Q b₀ : A} (hQ : IsIdempotentElem Q) (hxQ : Commute x Q)
    (hxb : Commute x b₀) (hQb : Commute Q b₀) (h : x * b₀ = Q) :
    ∃ b : A, x * b = Q ∧ b * x = Q ∧ Q * b = b ∧ b * Q = b := by
  refine ⟨Q * b₀, ?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, hxQ.eq, mul_assoc, h, hQ.eq]
  · rw [mul_assoc, ← hxb.eq, h, hQ.eq]
  · rw [← mul_assoc, hQ.eq]
  · rw [mul_assoc, ← hQb.eq, ← mul_assoc, hQ.eq]

/-- **The inner part has no spectrum outside the open disc.** For `‖μ‖ ≥ r`, the element
`μ - a` is invertible in the corner `P A P`, `P = rieszInner a r`. -/
theorem exists_inner_resolvent (hr : 0 < r) (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ a)
    {μ : ℂ} (hμ : r ≤ ‖μ‖) :
    ∃ b : A, (μ • (1 : A) - a) * b = rieszInner a r ∧ b * (μ • (1 : A) - a) = rieszInner a r ∧
      rieszInner a r * b = b ∧ b * rieszInner a r = b := by
  obtain ⟨δ, hδ, hδr, h⟩ := exists_annulus_subset_resolventSet hr hfree
  have hρ : 0 < r - δ / 2 := by linarith
  have hsρ := sphere_subset_resolventSet_of_annulus h (ρ := r - δ / 2) (by linarith)
    (by linarith)
  have heq : rieszInner a r = rieszInner a (r - δ / 2) :=
    rieszInner_eq_of_annulus hρ (by linarith) fun z h₁ h₂ ↦ h z (by linarith) (by linarith)
  have hμρ : r - δ / 2 < ‖μ‖ := by linarith
  have hd : ∀ z : ℂ, ‖z‖ ≤ r - δ / 2 → DifferentiableAt ℂ (fun z : ℂ ↦ (μ - z)⁻¹) z :=
    fun z hz ↦ by
      have hz' : μ - z ≠ 0 := fun h ↦ by rw [sub_eq_zero.mp h] at hμρ; linarith
      fun_prop (disch := exact hz')
  have hzero : (∮ z in C(0, r - δ / 2), (μ - z)⁻¹) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le countable_empty
      (fun z hz ↦ (hd z (mem_closedBall_zero_iff.mp hz)).continuousAt.continuousWithinAt)
      (fun z hz ↦ hd z (mem_ball_zero_iff.mp hz.1).le)
  have hx := smul_one_sub_mul_rieszIntegral_sub_inv hρ.le hsρ (μ := μ) hμρ.ne'
  rw [hzero, mul_zero, zero_smul, add_zero, ← heq] at hx
  have hcomm : Commute (μ • (1 : A) - a) a :=
    ((Commute.one_left a).smul_left μ).sub_left (Commute.refl a)
  exact exists_corner_inverse (rieszInner_idem hfree)
    (commute_rieszInner hcomm) (commute_rieszIntegral hcomm _ _)
    (commute_rieszIntegral (commute_rieszInner (Commute.refl a)).symm _ _) hx

/-- **The outer part has no spectrum in the closed disc.** For `‖μ‖ ≤ r`, the element `μ - a`
is invertible in the corner `(1 - P) A (1 - P)`, `P = rieszInner a r`. -/
theorem exists_outer_resolvent (hr : 0 < r) (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ a)
    {μ : ℂ} (hμ : ‖μ‖ ≤ r) :
    ∃ b : A, (μ • (1 : A) - a) * b = 1 - rieszInner a r ∧
      b * (μ • (1 : A) - a) = 1 - rieszInner a r ∧
      (1 - rieszInner a r) * b = b ∧ b * (1 - rieszInner a r) = b := by
  obtain ⟨δ, hδ, -, h⟩ := exists_annulus_subset_resolventSet hr hfree
  have hρ : 0 < r + δ / 2 := by linarith
  have hsρ := sphere_subset_resolventSet_of_annulus h (ρ := r + δ / 2) (by linarith)
    (by linarith)
  have heq : rieszInner a (r + δ / 2) = rieszInner a r :=
    rieszInner_eq_of_annulus hr (by linarith) fun z h₁ h₂ ↦ h z (by linarith) (by linarith)
  have hμρ : ‖μ‖ < r + δ / 2 := by linarith
  have hint : (2 * π * I)⁻¹ * (∮ z in C(0, r + δ / 2), (μ - z)⁻¹) = -1 := by
    have h2 := circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (mem_ball_zero_iff.mpr hμρ)
    have h3 : (∮ z in C(0, r + δ / 2), (μ - z)⁻¹) = -∮ z in C(0, r + δ / 2), (z - μ)⁻¹ := by
      rw [← neg_one_mul, ← circleIntegral.integral_const_mul]
      congr 1
      ext z
      rw [neg_one_mul, ← inv_neg, neg_sub]
    rw [h3, h2, mul_neg, inv_mul_cancel₀ two_pi_I_ne_zero]
  have hx := smul_one_sub_mul_rieszIntegral_sub_inv hρ.le hsρ (μ := μ) hμρ.ne
  rw [hint, heq, neg_one_smul] at hx
  have hx' : (μ • (1 : A) - a) * -rieszIntegral a (r + δ / 2) (fun z ↦ (μ - z)⁻¹) =
      1 - rieszInner a r := by
    rw [mul_neg, hx, neg_add, neg_neg, add_comm, ← sub_eq_add_neg]
  have hcomm : Commute (μ • (1 : A) - a) a :=
    ((Commute.one_left a).smul_left μ).sub_left (Commute.refl a)
  have hPa : Commute (1 - rieszInner a r) a :=
    (Commute.one_left a).sub_left (commute_rieszInner (Commute.refl a)).symm
  exact exists_corner_inverse (rieszInner_idem hfree).one_sub
    ((Commute.one_right _).sub_right (commute_rieszInner hcomm))
    (commute_rieszIntegral hcomm _ _).neg_right
    (commute_rieszIntegral hPa _ _).neg_right hx'

end PDE.Analysis.Spectral
