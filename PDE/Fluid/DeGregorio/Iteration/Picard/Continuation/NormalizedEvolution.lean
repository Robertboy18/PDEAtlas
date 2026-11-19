/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.LocalEvolution
import PDE.Fluid.DeGregorio.DynamicRescaling.PrincipalValue
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import CAS.ExactTactic

/-!
# H² propagation under endpoint normalization

The rate `-u(R)/R` is bounded by the H¹ size of the vorticity when `u(0) = 0`.
Thus a uniform H¹ bound controls equal endpoint-normalized rescaling rates and gives
exponential H² control for the rescaled equation with `a = 1`. The smooth energy
identity uses joint C³ vorticity.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis

namespace DeGregorio

/-- The endpoint-normalized rate is bounded by the H¹ size of the coupled
vorticity. The mean value theorem and Hilbert Sobolev estimate derive the bound. -/
theorem abs_endpoint_rate_le_h1 {w u : ℝ → ℝ} {R : ℝ}
    (hw : ContDiff ℝ 2 w) (hsupp : HasCompactSupport w)
    (hu : ContDiff ℝ 2 u) (hpair : IsHilbertPair w (deriv u))
    (hzero : u 0 = 0) (hR : 0 < R) :
    |-u R / R| ≤ lpNorm w 2 volume + lpNorm (deriv w) 2 volume := by
  have hbound := hpair.norm_le_eLpNorm_add_deriv
    (hu.continuous_deriv (by norm_num)) hw hsupp
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ (univ : Set ℝ)) ↦ (hu.differentiable (by norm_num)) x)
    (fun x _ ↦ hbound x) convex_univ (mem_univ 0) (mem_univ R)
  have hnorm : |u R| ≤ (lpNorm w 2 volume + lpNorm (deriv w) 2 volume) * R := by
    simpa only [hzero, sub_zero, Real.norm_eq_abs, abs_of_pos hR, toReal_eLpNorm] using h
  rw [abs_div, abs_neg, abs_of_pos hR]
  exact (div_le_iff₀ hR).mpr hnorm

/-- Compact C³ vorticity gives C³ velocity for a normalized rescaled solution.
Velocity regularity is recovered through the principal-value formula. -/
theorem IsClassicalRescaledSolutionOn.contDiff_three_velocity
    {a : ℝ} {fields : Fields} {cl cw : ℝ → ℝ} {times : Set ℝ}
    (hsol : IsClassicalRescaledSolutionOn a fields cl cw times) {t : ℝ} (ht : t ∈ times)
    (hw : ContDiff ℝ 3 (fun x ↦ fields.vorticity x t))
    (hsupp : HasCompactSupport (fun x ↦ fields.vorticity x t))
    (hzero : fields.velocity 0 t = 0) :
    ContDiff ℝ 3 (fun x ↦ fields.velocity x t) := by
  have hw₁ : ContDiff ℝ 1 (fun x ↦ fields.vorticity x t) := hw.of_le (by norm_num)
  rw [hsol.velocity_eq_hilbertPVVelocity ht hw₁ hsupp hzero]
  apply (contDiff_succ_iff_deriv (n := 2)).mpr
  refine ⟨fun x ↦
    (hasDerivAt_hilbertPVVelocity_of_contDiff_one_compactSupport hw₁ hsupp x).differentiableAt,
    by simp, ?_⟩
  rw [show deriv (hilbertPVVelocity (fun x ↦ fields.vorticity x t)) =
    hilbertPV (fun x ↦ fields.vorticity x t) from funext fun x ↦
      (hasDerivAt_hilbertPVVelocity_of_contDiff_one_compactSupport hw₁ hsupp x).deriv]
  exact contDiff_hilbertPV_of_contDiff_succ_compactSupport 2 hw hsupp

/-- For a smooth classical rescaled solution with equal endpoint-normalized
rates, a uniform H¹ bound alone gives exponential H² control on a finite interval. -/
theorem IsClassicalRescaledSolutionOn.sobolevEnergyTwo_le_exp_of_h1
    {fields : Fields} {ρ : ℝ → ℝ} {L R B t₀ T : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Icc t₀ T))
    (hw : ContDiff ℝ 3 (Function.uncurry fields.vorticity))
    (hu : ∀ t ∈ Icc t₀ T, ContDiff ℝ 3 (fun x ↦ fields.velocity x t))
    (hL : 0 ≤ L) (hR : 0 < R)
    (hsupp : ∀ t ∈ Icc t₀ T, tsupport (fun x ↦ fields.vorticity x t) ⊆ Ioo (-L) L)
    (hzero : ∀ t ∈ Icc t₀ T, fields.velocity 0 t = 0)
    (hnormalized : ∀ t ∈ Icc t₀ T, ρ t = -fields.velocity R t / R)
    (hinput : ∀ t ∈ Icc t₀ T,
      lpNorm (fun x ↦ fields.vorticity x t) 2 volume +
        lpNorm (deriv (fun x ↦ fields.vorticity x t)) 2 volume ≤ B) :
    ∀ t ∈ Icc t₀ T, sobolevEnergyTwo fields.vorticity L t ≤
      sobolevEnergyTwo fields.vorticity L t₀ * Real.exp (11 * B * (t - t₀)) := by
  have hrate (t : ℝ) (ht : t ∈ Icc t₀ T) : |ρ t| ≤ B := by
    rw [hnormalized t ht]
    have hwSlice : ContDiff ℝ 2 (fun x ↦ fields.vorticity x t) :=
      (hw.of_le (by norm_num)).comp (contDiff_id.prodMk contDiff_const)
    have hcompact : HasCompactSupport (fun x ↦ fields.vorticity x t) :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
        ((hsupp t ht).trans Ioo_subset_Icc_self)
    exact (abs_endpoint_rate_le_h1 hwSlice hcompact
      ((hu t ht).of_le (by norm_num)) (hsol.biotSavart ht) (hzero t ht) hR).trans
        (hinput t ht)
  have htransport (t : ℝ) (ht : t ∈ Icc t₀ T) (x : ℝ) :
      deriv (fields.vorticity x) t +
        (ρ t * x + fields.velocity x t) * deriv (fun y ↦ fields.vorticity y t) x =
          (ρ t + deriv (fun y ↦ fields.velocity y t) x) * fields.vorticity x t := by
    simpa only [one_mul] using hsol.transport (x := x) ht
  have h := sobolevEnergyTwo_le_exp_of_coupled_rescaled_transport hw hu
    (fun _ ht ↦ hsol.biotSavart ht) htransport hL hsupp hinput hrate
  have hcoef : 3 * B + 8 * B = 11 * B := by cas
  simpa only [hcoef] using h

/-- H¹ propagates H² for the endpoint-normalized rescaled equation on a half-open
trajectory, with C³ regularity assumed on `ℝ × (a, T)`. -/
theorem IsClassicalRescaledSolutionOn.sobolevEnergyTwo_le_exp_of_h1On
    {fields : Fields} {ρ : ℝ → ℝ} {L R B a t₀ T : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (hw : ContDiffOn ℝ 3 (Function.uncurry fields.vorticity) (univ ×ˢ Ioo a T))
    (ht₀ : t₀ ∈ Ioo a T)
    (hL : 0 ≤ L) (hR : 0 < R)
    (hsupp : ∀ t ∈ Ioo a T, tsupport (fun x ↦ fields.vorticity x t) ⊆ Ioo (-L) L)
    (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
    (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R)
    (hinput : ∀ t ∈ Ioo a T,
      lpNorm (fun x ↦ fields.vorticity x t) 2 volume +
        lpNorm (deriv (fun x ↦ fields.vorticity x t)) 2 volume ≤ B) :
    ∀ t ∈ Ico t₀ T, sobolevEnergyTwo fields.vorticity L t ≤
      sobolevEnergyTwo fields.vorticity L t₀ * Real.exp (11 * B * (t - t₀)) := by
  have hu (t : ℝ) (ht : t ∈ Ioo a T) :
      ContDiff ℝ 3 (fun x ↦ fields.velocity x t) := by
    apply hsol.contDiff_three_velocity ht
    · exact hw.comp_contDiff (contDiff_id.prodMk contDiff_const)
        (fun x ↦ ⟨mem_univ x, ht⟩)
    · exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
        ((hsupp t ht).trans Ioo_subset_Icc_self)
    · exact hzero t ht
  have hrate (t : ℝ) (ht : t ∈ Ioo a T) : |ρ t| ≤ B := by
    rw [hnormalized t ht]
    have hwSlice : ContDiff ℝ 2 (fun x ↦ fields.vorticity x t) :=
      (hw.of_le (by norm_num)).comp_contDiff (contDiff_id.prodMk contDiff_const)
        (fun x ↦ ⟨mem_univ x, ht⟩)
    have hcompact : HasCompactSupport (fun x ↦ fields.vorticity x t) :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
        ((hsupp t ht).trans Ioo_subset_Icc_self)
    exact (abs_endpoint_rate_le_h1 hwSlice hcompact
      ((hu t ht).of_le (by norm_num)) (hsol.biotSavart ht) (hzero t ht) hR).trans
        (hinput t ht)
  have htransport (t : ℝ) (ht : t ∈ Ioo a T) (x : ℝ) :
      deriv (fields.vorticity x) t +
        (ρ t * x + fields.velocity x t) * deriv (fun y ↦ fields.vorticity y t) x =
          (ρ t + deriv (fun y ↦ fields.velocity y t) x) * fields.vorticity x t := by
    simpa only [one_mul] using hsol.transport (x := x) ht
  have h := sobolevEnergyTwo_le_exp_of_coupled_rescaled_transportOn hw ht₀ hu
    (fun _ ht ↦ hsol.biotSavart ht) htransport hL hsupp hinput hrate
  have hcoef : 3 * B + 8 * B = 11 * B := by cas
  simpa only [hcoef] using h

/-- H¹ controls the H² energy uniformly up to a finite terminal time for a
smooth endpoint-normalized rescaled trajectory. The bound is obtained from the
energy at one interior time. -/
theorem IsClassicalRescaledSolutionOn.sobolevEnergyTwo_uniform_bound_of_h1On
    {fields : Fields} {ρ : ℝ → ℝ} {L R B a t₀ T : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (hw : ContDiffOn ℝ 3 (Function.uncurry fields.vorticity) (univ ×ˢ Ioo a T))
    (ht₀ : t₀ ∈ Ioo a T) (hL : 0 ≤ L) (hR : 0 < R)
    (hsupp : ∀ t ∈ Ioo a T, tsupport (fun x ↦ fields.vorticity x t) ⊆ Ioo (-L) L)
    (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
    (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R)
    (hinput : ∀ t ∈ Ioo a T,
      lpNorm (fun x ↦ fields.vorticity x t) 2 volume +
        lpNorm (deriv (fun x ↦ fields.vorticity x t)) 2 volume ≤ B) :
    ∀ t ∈ Ico t₀ T, sobolevEnergyTwo fields.vorticity L t ≤
      sobolevEnergyTwo fields.vorticity L t₀ * Real.exp (11 * B * (T - t₀)) := by
  have hB : 0 ≤ B :=
    (add_nonneg lpNorm_nonneg lpNorm_nonneg).trans (hinput t₀ ht₀)
  intro t ht
  apply (hsol.sobolevEnergyTwo_le_exp_of_h1On hw ht₀ hL hR hsupp hzero
    hnormalized hinput t ht).trans
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le t₀)
      (mul_nonneg (by norm_num) hB))) (sobolevEnergyTwo_nonneg fields.vorticity L t₀)

end DeGregorio
