/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.PorousMedium.Profile
public import PDE.Analysis.Calculus.ParametricIntegral.CompactSupport
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Testing the Barenblatt profile on a fixed integration domain

The change of variables `x = t^β y` turns a moving-support density integral
into an integral over the fixed compact support of the profile. Differentiation
therefore needs only continuity of the density, even when its classical
derivative is singular at the free boundary.
-/

@[expose] public noncomputable section

namespace PorousMedium

open MeasureTheory Set Filter
open scoped Topology

variable {n : ℕ}

/-- The derivative of a test function along the expanding similarity coordinates,
weighted by the fixed profile. The derivative is the spacetime Fréchet derivative. -/
def profileTestDerivative (n : ℕ) (m C : ℝ) (ψ : ℝ × ℝ^n → ℝ)
    (t : ℝ) (y : ℝ^n) : ℝ :=
  profile n m C y *
    fderiv ℝ ψ (t, t ^ similarityBeta n m • y)
      (1, (similarityBeta n m * t ^ (similarityBeta n m - 1)) • y)

/-- The spatial dilation has its expected time derivative. -/
theorem hasDerivAt_similarity_radius (n : ℕ) (m : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ s ^ similarityBeta n m)
      (similarityBeta n m * t ^ (similarityBeta n m - 1)) t := by
  cas using ht

/-- Chain rule for the profile-weighted test function along the expanding coordinates. -/
theorem hasDerivAt_profile_test (m C : ℝ) {ψ : ℝ × ℝ^n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) {t : ℝ} (ht : 0 < t) (y : ℝ^n) :
    HasDerivAt
      (fun s ↦ profile n m C y * ψ (s, s ^ similarityBeta n m • y))
      (profileTestDerivative n m C ψ t y) t := by
  exact (((hψ.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk ((hasDerivAt_similarity_radius n m ht).smul_const y))).const_mul _

private theorem continuousOn_similarity_coordinates (m : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ^n ↦ (p.1, p.1 ^ similarityBeta n m • p.2))
      (Ioi 0 ×ˢ univ) := by
  exact continuousOn_fst.prodMk
    ((continuousOn_fst.rpow_const (fun p hp ↦ Or.inl (ne_of_gt hp.1))).smul continuousOn_snd)

private theorem continuousOn_similarity_velocity (m : ℝ) :
    ContinuousOn
      (fun p : ℝ × ℝ^n ↦ ((1 : ℝ), (similarityBeta n m *
        p.1 ^ (similarityBeta n m - 1)) • p.2))
      (Ioi 0 ×ˢ univ) := by
  exact continuousOn_const.prodMk
    ((continuousOn_const.mul
      (continuousOn_fst.rpow_const (fun p hp ↦ Or.inl (ne_of_gt hp.1)))).smul
        continuousOn_snd)

/-- Joint continuity of the integrand differentiated on the fixed profile domain. -/
theorem continuousOn_profileTestDerivative {m : ℝ} (hm : 1 < m) (C : ℝ)
    {ψ : ℝ × ℝ^n → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    ContinuousOn (profileTestDerivative n m C ψ).uncurry (Ioi 0 ×ˢ univ) := by
  exact ((continuous_profile hm C).comp_continuousOn continuousOn_snd).mul
    (((hψ.continuous_fderiv (by norm_num)).comp_continuousOn
      (continuousOn_similarity_coordinates m)).clm_apply (continuousOn_similarity_velocity m))

/-- Differentiation under the fixed compact profile integral is valid at every positive time. -/
theorem hasDerivAt_integral_profile_test {m C : ℝ} (hm : 1 < m)
    {ψ : ℝ × ℝ^n → ℝ} (hψ : ContDiff ℝ 1 ψ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s ↦ ∫ y : ℝ^n, profile n m C y * ψ (s, s ^ similarityBeta n m • y))
      (∫ y, profileTestDerivative n m C ψ t y) t := by
  apply PDE.hasDerivAt_integral_of_locally_uniform_compact_support
    isOpen_Ioi (hasCompactSupport_profile (C := C) hm).isCompact ?_
    (continuousOn_profileTestDerivative hm C hψ) ?_ ?_ ht
  · exact ((continuous_profile hm C).comp_continuousOn continuousOn_snd).mul
      (hψ.continuous.comp_continuousOn (continuousOn_similarity_coordinates m))
  · intro s hs y
    exact hasDerivAt_profile_test m C hψ hs y
  · intro s _ y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

/-- The integrated derivative is continuous for positive time, with compact support
providing the local domination. -/
theorem continuousOn_integral_profileTestDerivative {m C : ℝ}
    (hm : 1 < m) {ψ : ℝ × ℝ^n → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    ContinuousOn (fun t ↦ ∫ y, profileTestDerivative n m C ψ t y) (Ioi 0) := by
  apply continuousOn_integral_of_compact_support
    (hasCompactSupport_profile (C := C) hm).isCompact
    (continuousOn_profileTestDerivative hm C hψ)
  intro t y _ hy
  rw [profileTestDerivative, image_eq_zero_of_notMem_tsupport hy, zero_mul]

/-- The fixed-domain test identity integrated between two positive times. -/
theorem integral_profileTestDerivative {m C a b : ℝ}
    (hm : 1 < m) (ha : 0 < a) (hab : a ≤ b)
    {ψ : ℝ × ℝ^n → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    (∫ t in a..b, ∫ y, profileTestDerivative n m C ψ t y) =
      (∫ y : ℝ^n, profile n m C y * ψ (b, b ^ similarityBeta n m • y)) -
        ∫ y : ℝ^n, profile n m C y * ψ (a, a ^ similarityBeta n m • y) := by
  have hpos : uIcc a b ⊆ Ioi (0 : ℝ) := by
    rw [uIcc_of_le hab]
    exact fun t ht ↦ lt_of_lt_of_le ha ht.1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_integral_profile_test hm hψ (hpos ht))
  exact ((continuousOn_integral_profileTestDerivative hm hψ).mono hpos).intervalIntegrable

end PorousMedium
