/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Interior.Estimates.Cutoffs
public import PDE.Parabolic.Heat.Interior.TimeCutoff
import PDE.Parabolic.Heat.Duhamel.KernelLocalization

/-!
# A fixed compact kernel representing local heat solutions

The cutoff residual vanishes near the half cylinder and has a common
compact spatial support. The fixed kernel constructed in `Estimates.Cutoffs`
therefore represents the field near that cylinder, including its terminal
time. The construction uses only the original continuous classical jets.
-/

@[expose] public section

open PDE (laplacian)

open MeasureTheory Metric Set
open scoped Interval

namespace HeatEquation

variable {n : ℕ}

/-- The compact replacement kernel represents a local heat field near the
half cylinder. Its agreement region comes from
`exists_compact_heatKernel_on_unitCutoff` and does not depend on the field. -/
theorem unitCutoff_eq_kernel_integral
    {G : ℝ^n × ℝ → ℝ} (hG : Continuous G)
    (hmatch : ∀ (x y : ℝ^n) (t s : ℝ),
      ‖x‖ < 5 / 8 → -3 / 8 < t → t ≤ 0 →
      ‖y‖ ≤ 7 / 8 → -1 ≤ s → s ≤ 0 →
      (3 / 4 ≤ ‖y‖ ∨ s ≤ -1 / 2) →
      G ((x, t) - (y, s)) = fundamentalSolutionHeat (x - y) (t - s))
    {Ω : Set (ℝ^n)} {u : ℝ^n → ℝ → ℝ}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ}
    {Dt : ℝ^n × ℝ → ℝ}
    (hΩ : IsOpen Ω) (hball : closedBall 0 1 ⊆ Ω)
    (hu : ContinuousOn u.uncurry (Ω ×ˢ Icc (-1) 0))
    (hDx : ContinuousOn Dx (Ω ×ˢ Icc (-1) 0))
    (hDxx : ContinuousOn Dxx (Ω ×ˢ Icc (-1) 0))
    (hDt : ContinuousOn Dt (Ω ×ˢ Icc (-1) 0))
    (hspace : ∀ p ∈ Ω ×ˢ Icc (-1) 0,
      HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1)
    (hhessian : ∀ p ∈ Ω ×ˢ Icc (-1) 0,
      HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1)
    (htime : ∀ p ∈ Ω ×ˢ Icc (-1) 0,
      HasDerivWithinAt (u p.1) (Dt p) (Icc (-1) 0) p.2)
    (hheat : ∀ p ∈ Ω ×ˢ Icc (-1) 0,
      Dt p - laplacian (fun y ↦ u y p.2) p.1 = 0)
    {x : ℝ^n} {t : ℝ} (hx : ‖x‖ < 5 / 8) (ht : -3 / 8 < t) (ht0 : t ≤ 0) :
    u x t = ∫ q in tsupport (unitSpatialCutoff n) ×ˢ Icc (-1) 0,
      (deriv unitTimeCutoff q.2 * (unitSpatialCutoff n q.1 * u q.1 q.2) +
        unitTimeCutoff q.2 * (unitSpatialCutoff n q.1 * Dt q -
          laplacian (fun z ↦ unitSpatialCutoff n z * u z q.2) q.1)) *
            G ((x, t) - q) := by
  let χ := unitSpatialCutoff n
  let R : ℝ^n × ℝ → ℝ := fun q ↦
    deriv unitTimeCutoff q.2 * (χ q.1 * u q.1 q.2) +
      unitTimeCutoff q.2 * (χ q.1 * Dt q -
        laplacian (fun z ↦ χ z * u z q.2) q.1)
  have hχΩ : tsupport χ ⊆ Ω := fun y hy ↦ hball
    (closedBall_subset_closedBall (by norm_num [χ, unitSpatialCutoff]) (χ.tsupport_eq ▸ hy))
  have hR : ContinuousOn R (univ ×ˢ Icc (-1) 0) :=
    continuousOn_spaceTimeCutoff_heatResidual hΩ hu hDx hDxx hDt hspace hhessian
      χ.contDiff hχΩ contDiff_unitTimeCutoff
  have hsupport (s : ℝ) (_hs : s ∈ Icc (-1) 0) (y : ℝ^n) (hy : y ∉ tsupport χ) :
      R (y, s) = 0 := by
    have hres := spatialCutoff_heatResidual_eq_zero_of_notMem_tsupport
      (u := fun z ↦ u z s) (Dt (y, s)) hy
    change deriv unitTimeCutoff s * (χ y * u y s) +
      unitTimeCutoff s * (χ y * Dt (y, s) - laplacian (fun z ↦ χ z * u z s) y) = 0
    rw [hres, image_eq_zero_of_notMem_tsupport hy, zero_mul, mul_zero, mul_zero, add_zero]
  have hxΩ : x ∈ Ω := hball (mem_closedBall_zero_iff.2 (by linarith))
  have hat : -1 ≤ t := by linarith
  have hfuture (s : ℝ) (hs : s ∈ Icc t 0) : R (x, s) = 0 :=
    unitCutoff_heatResidual_eq_zero (by linarith) (by linarith [hs.1])
      (hheat (x, s) ⟨hxΩ, hat.trans hs.1, hs.2⟩)
  have hkernel (q : ℝ^n × ℝ) (hq : q ∈ tsupport χ ×ˢ Icc (-1) 0) :
      R q * G ((x, t) - q) =
        R q * fundamentalSolutionHeat (x - q.1) (t - q.2) := by
    by_cases hsource : 3 / 4 ≤ ‖q.1‖ ∨ q.2 ≤ -1 / 2
    · have hy : ‖q.1‖ ≤ 7 / 8 := by
        have hqχ := hq.1
        rw [χ.tsupport_eq] at hqχ
        simpa only [χ, unitSpatialCutoff, mem_closedBall, dist_zero_right] using hqχ
      rw [hmatch x q.1 t q.2 hx ht ht0 hy hq.2.1 hq.2.2 hsource]
    · have hzero : R q = 0 := unitCutoff_heatResidual_eq_zero
        (lt_of_not_ge (not_or.mp hsource).1) (lt_of_not_ge (not_or.mp hsource).2)
        (hheat q ⟨hχΩ hq.1, hq.2⟩)
      rw [hzero, zero_mul, zero_mul]
  have hpot := integral_kernel_eq_duhamel hat ht0 χ.hasCompactSupport hR hG
    hsupport hfuture hkernel
  have hsub : Ω ×ˢ Icc (-1) t ⊆ Ω ×ˢ Icc (-1) 0 :=
    prod_mono_right (Icc_subset_Icc le_rfl ht0)
  have hid := spaceTimeCutoff_eq_integral_heatResidual hat hΩ (hu.mono hsub)
    (hDx.mono hsub) (hDxx.mono hsub) (hDt.mono hsub)
    (fun q hq ↦ hspace q (hsub hq)) (fun q hq ↦ hhessian q (hsub hq))
    (fun q hq ↦ (htime q (hsub hq)).mono (Icc_subset_Icc le_rfl ht0))
    χ.contDiff χ.hasCompactSupport hχΩ (contDiff_unitTimeCutoff (m := 1))
    (unitTimeCutoff_eq_zero (by norm_num)) x
  have hχx : χ x = 1 := χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 (by
    change ‖x‖ ≤ 3 / 4
    linarith))
  have hηt : unitTimeCutoff t = 1 := unitTimeCutoff_eq_one (by linarith)
  change u x t = ∫ q in tsupport χ ×ˢ Icc (-1) 0, R q * G ((x, t) - q)
  rw [hpot]
  simpa only [hηt, hχx, one_mul, R] using hid

end HeatEquation
