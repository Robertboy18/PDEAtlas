/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.PorousMedium.Profile
public import PDE.Representations.Similarity.Calculus
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import CAS.ExactTactic

/-!
# The Barenblatt family, its conserved mass and its global flux

`barenblatt n m C t x = t^(-α) F(t^(-β) x)` is the similarity ansatz with the Barenblatt profile `F`
(`barenblatt_eq`). At every positive time it is continuous, nonnegative, compactly supported and
integrable; it is positive on the open ball of radius `supportRadius n m C t` and zero outside it
(`barenblatt_pos_iff_norm_lt`, `support_barenblatt_ball`). Its integral is the profile mass at every
positive time (`integral_barenblatt`), because the amplitude cancels the Jacobian of the dilation
(`similarity_jacobian_balance`). The potential `u^m` is `C¹` across the moving interface
(`contDiff_barenblatt_potential`), and the diffusion balance gives `∇(u^m)(x) = -(β/t) u(x) x`
(`gradient_barenblatt_potential`). SymLean's `cas` tactic checks the exponent identities.

This is the Barenblatt-Kompaneetz-Zeldovich solution (35)-(36) of Evans's §4.2.2, with `γ = m` and
`b = C`. Evans does not compute its mass; `integral_barenblatt` shows that his choice `α = nβ` in
(33) conserves it.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.2.2, Example (A scaling invariant solution), (27)-(36),
  pp. 185-186.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PorousMedium

open MeasureTheory Set PDE.Representations.Similarity
open scoped Gradient RealInnerProductSpace

variable {n : ℕ}

/-- The Barenblatt solution candidate, expressed using the shared similarity ansatz. -/
def barenblatt (n : ℕ) (m C t : ℝ) (x : ℝ^n) : ℝ :=
  forwardSelfSimilarAnsatz (profile n m C) (-similarityAlpha n m)
    (similarityBeta n m) 0 x t

/-- The explicit compactly supported similarity formula. -/
theorem barenblatt_eq (m C t : ℝ) (x : ℝ^n) :
    barenblatt n m C t x =
      t ^ (-similarityAlpha n m) *
        profile n m C ((t ^ similarityBeta n m)⁻¹ • x) := by
  simp [barenblatt, forwardSelfSimilarAnsatz, scaledProfileAnsatz, centeredDilation]

/-- The amplitude cancels the Jacobian of the spatial dilation. -/
theorem similarity_jacobian_balance (n : ℕ) (m : ℝ) {t : ℝ} (ht : 0 < t) :
    t ^ (-similarityAlpha n m) * (t ^ similarityBeta n m) ^ n = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  have he : -similarityAlpha n m + similarityBeta n m * (n : ℝ) = 0 := by
    unfold similarityAlpha
    cas
  rw [he, Real.rpow_zero]

/-- Diffusion balance converts two spatial factors into the time factor. -/
theorem similarity_flux_scaling {m t : ℝ} (hm : 1 < m) (ht : 0 < t) :
    (t ^ (-similarityAlpha n m)) ^ m *
        (t ^ similarityBeta n m)⁻¹ * (t ^ similarityBeta n m)⁻¹ =
      t ^ (-similarityAlpha n m) / t := by
  rw [← Real.rpow_mul ht.le, ← Real.rpow_neg ht.le,
    ← Real.rpow_add ht, ← Real.rpow_add ht]
  have he : -similarityAlpha n m * m + -similarityBeta n m + -similarityBeta n m =
      -similarityAlpha n m - 1 := by
    have hb := similarity_diffusion_balance n hm
    cas using hb
  rw [he, Real.rpow_sub_one ht.ne']

/-- The Barenblatt density is nonnegative at positive time. -/
theorem barenblatt_nonneg (m C : ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ^n) :
    0 ≤ barenblatt n m C t x := by
  rw [barenblatt_eq]
  exact mul_nonneg (Real.rpow_pos_of_pos ht _).le (profile_nonneg m C _)

/-- The strict positivity region follows the moving similarity ball. -/
theorem barenblatt_pos_iff {m t : ℝ} (hm : 1 < m) (C : ℝ) (ht : 0 < t)
    (x : ℝ^n) :
    0 < barenblatt n m C t x ↔
      profileCoefficient n m * ‖(t ^ similarityBeta n m)⁻¹ • x‖ ^ 2 < C := by
  rw [barenblatt_eq, mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos ht _),
    profile_pos_iff hm]

/-- The nonzero support is the moving positivity region. -/
theorem support_barenblatt {m t : ℝ} (hm : 1 < m) (C : ℝ) (ht : 0 < t) :
    Function.support (barenblatt n m C t) =
      {x : ℝ^n | profileCoefficient n m *
        ‖(t ^ similarityBeta n m)⁻¹ • x‖ ^ 2 < C} := by
  ext x
  simp [Function.mem_support, barenblatt_eq,
    (Real.rpow_pos_of_pos ht (-similarityAlpha n m)).ne', profile_eq_zero_iff hm]

/-- The finite propagation radius of the Barenblatt density at positive time. -/
def supportRadius (n : ℕ) (m C t : ℝ) : ℝ :=
  t ^ similarityBeta n m * Real.sqrt (C / profileCoefficient n m)

/-- The positivity region is the open ball with the expanding support radius. -/
theorem barenblatt_pos_iff_norm_lt {m t : ℝ} (hm : 1 < m) (C : ℝ) (ht : 0 < t)
    (x : ℝ^n) :
    0 < barenblatt n m C t x ↔ ‖x‖ < supportRadius n m C t := by
  have hr := Real.rpow_pos_of_pos ht (similarityBeta n m)
  rw [barenblatt_pos_iff hm C ht, ← lt_div_iff₀' (profileCoefficient_pos n hm),
    ← Real.lt_sqrt (norm_nonneg _), norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr), ← div_eq_inv_mul, div_lt_iff₀ hr, supportRadius, mul_comm]

/-- The support as nonzero points is the open expanding ball. -/
theorem support_barenblatt_ball {m t : ℝ} (hm : 1 < m) (C : ℝ) (ht : 0 < t) :
    Function.support (barenblatt n m C t) =
      Metric.ball (0 : ℝ^n) (supportRadius n m C t) := by
  ext x
  rw [Function.mem_support, ne_comm, ← (barenblatt_nonneg m C ht x).lt_iff_ne,
    barenblatt_pos_iff_norm_lt hm C ht]
  simp only [Metric.mem_ball, dist_zero_right]

/-- Every positive-time density has compact support, including the interface. -/
theorem hasCompactSupport_barenblatt {m t : ℝ} (hm : 1 < m) (C : ℝ) (ht : 0 < t) :
    HasCompactSupport (barenblatt n m C t) := by
  apply HasCompactSupport.intro
    (isCompact_closedBall (0 : ℝ^n) (supportRadius n m C t))
  intro x hx
  apply Function.notMem_support.mp
  rw [support_barenblatt_ball hm C ht]
  exact fun hball ↦ hx (Metric.ball_subset_closedBall hball)

/-- Every positive-time slice is continuous. -/
theorem continuous_barenblatt {m : ℝ} (hm : 1 < m) (C t : ℝ) :
    Continuous (barenblatt n m C t) := by
  change Continuous (fun x ↦ barenblatt n m C t x)
  simp_rw [barenblatt_eq]
  exact continuous_const.mul ((continuous_profile hm C).comp (by fun_prop))

/-- The density has a finite Lebesgue integral at each positive time. -/
theorem integrable_barenblatt {m C t : ℝ} (hm : 1 < m) (ht : 0 < t) :
    Integrable (barenblatt n m C t) := by
  change Integrable (fun x ↦ barenblatt n m C t x)
  simp_rw [barenblatt_eq]
  exact ((integrable_profile hm).comp_smul
    (inv_ne_zero (Real.rpow_pos_of_pos ht _).ne')).const_mul _

/-- Dilation transports the weighted density integral to the fixed profile domain. -/
theorem integral_barenblatt_mul (m C : ℝ) {t : ℝ} (ht : 0 < t) (g : ℝ^n → ℝ) :
    (∫ x, barenblatt n m C t x * g x) =
      ∫ y, profile n m C y * g ((t ^ similarityBeta n m) • y) := by
  have hr := (Real.rpow_pos_of_pos ht (similarityBeta n m)).ne'
  have hchange := Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure (ℝ^n))
    (fun y ↦ profile n m C y * g ((t ^ similarityBeta n m) • y))
    (Real.rpow_pos_of_pos ht (similarityBeta n m)).le
  simp only [smul_smul, mul_inv_cancel₀ hr, one_smul, finrank_euclideanSpace_fin,
    smul_eq_mul] at hchange
  simp_rw [barenblatt_eq, mul_assoc]
  rw [integral_const_mul, hchange, ← mul_assoc, similarity_jacobian_balance n m ht,
    one_mul]

/-- The profile mass is conserved at every positive time. -/
theorem integral_barenblatt {m C t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ^n, barenblatt n m C t x) = profileMass n m C := by
  simpa only [mul_one, profileMass] using integral_barenblatt_mul m C ht (fun _ ↦ 1)

/-- The diffusion potential is the dilated `C¹` profile potential. -/
theorem barenblatt_potential_eq {t : ℝ} (ht : 0 < t) (m C : ℝ) (x : ℝ^n) :
    barenblatt n m C t x ^ m =
      scaledProfileAnsatz (fun y : ℝ^n ↦ profile n m C y ^ m)
        (fun s ↦ (s ^ (-similarityAlpha n m)) ^ m)
        (fun s ↦ (s ^ similarityBeta n m)⁻¹) 0 x t := by
  rw [barenblatt_eq, Real.mul_rpow (Real.rpow_pos_of_pos ht _).le
    (profile_nonneg m C _)]
  simp [scaledProfileAnsatz, centeredDilation]

/-- The diffusion potential remains `C¹` across the moving free boundary. -/
theorem contDiff_barenblatt_potential {m t : ℝ} (hm : 1 < m) (ht : 0 < t) (C : ℝ) :
    ContDiff ℝ 1 (fun x : ℝ^n ↦ barenblatt n m C t x ^ m) := by
  simp_rw [barenblatt_potential_eq ht]
  exact contDiff_scaled_profile_ansatz_slice _ _ _ _ _ (contDiff_profile_potential hm C)

/-- The diffusion flux is the outward dilation velocity times minus the density. -/
theorem gradient_barenblatt_potential {m t : ℝ} (hm : 1 < m) (ht : 0 < t)
    (C : ℝ) (x : ℝ^n) :
    ∇ (fun z : ℝ^n ↦ barenblatt n m C t z ^ m) x =
      (-(similarityBeta n m / t) * barenblatt n m C t x) • x := by
  simp_rw [barenblatt_potential_eq ht]
  rw [gradient_scaled_profile_ansatz _ _ _ _ _ _
    ((contDiff_profile_potential hm C).differentiable (by norm_num)).differentiableAt,
    gradient_profile_potential hm]
  simp only [centeredDilation, sub_zero, smul_smul, barenblatt_eq]
  congr 1
  have hb := similarity_flux_scaling (n := n) hm ht
  have ht0 := ht.ne'
  have hr := (Real.rpow_pos_of_pos ht (similarityBeta n m)).ne'
  field_simp at hb ⊢
  cas using hb

end PorousMedium
