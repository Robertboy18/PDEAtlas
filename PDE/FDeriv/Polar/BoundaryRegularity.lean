/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Polar.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Polar regularity up to the horizontal boundary

A separated field `a(r) f(β)` with `C²` scalar factors is `C²` within the
closed upper half-plane when `a` vanishes near zero. At the negative horizontal
axis the ordinary polar chart has a branch cut. Rotating the point by pi puts
it in the positive chart; adding pi to the resulting angle gives a local smooth
formula agreeing on the physical side. No condition on unused negative angular
values is needed.
-/

@[expose] public noncomputable section

namespace PDE.FDeriv

open PDE.CoordinateSystems (meridianR meridianZ)
open PDE.Common (coordinateClosedHalfSpace)
open scoped Topology

/-- On the closed upper half-plane to the left of the origin, rotation by pi
moves the chart angle into a neighborhood of zero. -/
theorem polarCoord_pointPair_neg_snd_add_pi {x : ℝ^2}
    (hleft : x 0 < 0) (hupper : 0 ≤ x 1) :
    (polarCoord (pointPair (-x))).2 + Real.pi = (polarCoord (pointPair x)).2 := by
  let z : ℂ := Complex.equivRealProd.symm (pointPair x)
  have hzneg : Complex.equivRealProd.symm (pointPair (-x)) = -z := by
    apply Complex.ext <;>
      simp [z, Complex.equivRealProd_symm_apply, pointPair, meridianR, meridianZ]
  change Complex.arg (Complex.equivRealProd.symm (pointPair (-x))) + Real.pi = z.arg
  rw [hzneg]
  by_cases haxis : x 1 = 0
  · have hzreal : z = (x 0 : ℂ) := by
      apply Complex.ext <;> simp [z, Complex.equivRealProd_symm_apply, pointPair,
        meridianR, meridianZ, haxis]
    rw [hzreal, ← Complex.ofReal_neg, Complex.arg_ofReal_of_nonneg (by linarith),
      Complex.arg_ofReal_of_neg hleft, zero_add]
  · have him : 0 < z.im := by
      simpa [z, Complex.equivRealProd_symm_apply, pointPair, meridianR, meridianZ] using
        lt_of_le_of_ne' hupper haxis
    rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos him]
    ring

/-- The pi-rotated reconstruction agrees with the original physical formula
on the left part of the closed upper half-plane. -/
theorem profileFromPolar_mul_neg_shift_pi {a f : ℝ → ℝ} {x : ℝ^2}
    (hleft : x 0 < 0) (hupper : 0 ≤ x 1) :
    profileFromPolar (fun r β ↦ a r * f (β + Real.pi)) (-x) =
      profileFromPolar (fun r β ↦ a r * f β) x := by
  simp only [profileFromPolar, polarCoord_pointPair_fst, norm_neg]
  rw [polarCoord_pointPair_neg_snd_add_pi hleft hupper]

/-- Separated scalar `C²` factors reconstruct a `C²` field within the closed
upper half-plane, including its branch-cut boundary and the cutoff origin. -/
theorem contDiffOn_profileFromPolar_mul_closed_upper
    {a f : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hf : ContDiff ℝ 2 f)
    (hzero : a =ᶠ[𝓝 0] fun _ ↦ 0) :
    ContDiffOn ℝ 2 (profileFromPolar (fun r β ↦ a r * f β))
      (coordinateClosedHalfSpace (1 : Fin 2)) := by
  intro x hx
  have hupper : 0 ≤ x 1 := hx
  by_cases hzeroPoint : x = 0
  · subst x
    have hnorm : Filter.Tendsto (fun y : ℝ^2 ↦ ‖y‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
      simpa only [norm_zero] using continuous_norm.tendsto (0 : ℝ^2)
    have heq : profileFromPolar (fun r β ↦ a r * f β) =ᶠ[𝓝 0] fun _ ↦ 0 := by
      filter_upwards [hnorm.eventually hzero] with y hy
      simp only [profileFromPolar, polarCoord_pointPair_fst, hy, zero_mul]
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt
  · by_cases hleft : x 0 < 0
    · have hsource : pointPair (-x) ∈ polarCoord.source := by
        left
        change 0 < -x 0
        linarith
      have hshift : ContDiff ℝ 2 (fun β ↦ f (β + Real.pi)) :=
        hf.comp (contDiff_id.add contDiff_const)
      have halt : ContDiffAt ℝ 2
          (fun y : ℝ^2 ↦ profileFromPolar (fun r β ↦ a r * f (β + Real.pi)) (-y)) x :=
        (contDiffAt_profileFromPolar _ hsource
          ((ha.contDiffAt.comp _ contDiffAt_fst).mul
            (hshift.contDiffAt.comp _ contDiffAt_snd))).comp x contDiffAt_id.neg
      have hleftNear : ∀ᶠ y : ℝ^2 in 𝓝 x, y 0 < 0 :=
        (EuclideanSpace.proj (0 : Fin 2)).continuous.tendsto x |>.eventually (gt_mem_nhds hleft)
      have heq :
          profileFromPolar (fun r β ↦ a r * f β) =ᶠ[𝓝[coordinateClosedHalfSpace (1 : Fin 2)] x]
            (fun y ↦ profileFromPolar (fun r β ↦ a r * f (β + Real.pi)) (-y)) := by
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hleftNear]
          with y hy hyl
        exact (profileFromPolar_mul_neg_shift_pi hyl hy).symm
      exact halt.contDiffWithinAt.congr_of_eventuallyEq heq
        (profileFromPolar_mul_neg_shift_pi hleft hupper).symm
    · have hsource : pointPair x ∈ polarCoord.source := by
        by_cases hfirst : x 0 = 0
        · right
          intro hsecond
          apply hzeroPoint
          ext i
          fin_cases i
          · exact hfirst
          · exact hsecond
        · left
          change 0 < x 0
          exact lt_of_le_of_ne' (le_of_not_gt hleft) hfirst
      exact (contDiffAt_profileFromPolar _ hsource
        ((ha.contDiffAt.comp _ contDiffAt_fst).mul
          (hf.contDiffAt.comp _ contDiffAt_snd))).contDiffWithinAt

/-- A scalar cutoff zero near the origin removes the singularity of every real
power while retaining two continuous derivatives. -/
theorem contDiff_cutoff_mul_rpow
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (hflat : χ =ᶠ[𝓝 0] fun _ ↦ 0) (m : ℝ) :
    ContDiff ℝ 2 (fun r ↦ χ r * r ^ m) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : r = 0
  · subst r
    have heq : (fun s : ℝ ↦ χ s * s ^ m) =ᶠ[𝓝 0] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hflat] with s hs
      simp only [hs, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact hχ.contDiffAt.mul (Real.contDiffAt_rpow_const_of_ne hr)

/-- A cutoff homogeneous streamfunction is `C²` within the closed physical
upper half-plane without matching the unused angular branch endpoints. -/
theorem contDiffOn_profileFromPolar_cutoff_rpow_mul_closed_upper
    {χ f : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (hf : ContDiff ℝ 2 f)
    (hflat : χ =ᶠ[𝓝 0] fun _ ↦ 0) (m : ℝ) :
    ContDiffOn ℝ 2 (profileFromPolar (fun r β ↦ χ r * (r ^ m * f β)))
      (coordinateClosedHalfSpace (1 : Fin 2)) := by
  have hzero : (fun r ↦ χ r * r ^ m) =ᶠ[𝓝 0] fun _ ↦ 0 := by
    filter_upwards [hflat] with r hr
    simp only [hr, zero_mul]
  simpa only [mul_assoc] using
    contDiffOn_profileFromPolar_mul_closed_upper (contDiff_cutoff_mul_rpow hχ hflat m) hf hzero

end PDE.FDeriv
