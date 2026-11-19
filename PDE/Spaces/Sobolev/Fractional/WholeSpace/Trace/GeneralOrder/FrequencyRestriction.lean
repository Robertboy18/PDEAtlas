/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.GeneralOrder.FrequencyLifting
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.NormalIntegral

/-!
# General-order restriction as a normal-frequency integral

The adjoint of kernel multiplication is a contraction with a right inverse.
The fiberwise Cauchy–Schwarz estimate and Fubini identify it with the
normal integral, including absolute integrability on almost every fiber.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace SobolevSpace.Fractional.Trace.GeneralOrder

variable {n : ℕ} {s : ℝ}

/-- The adjoint restriction in normalized Fourier coordinates. -/
def frequencyRestriction (n : ℕ) (hs : 1 / 2 < s) :
    Lp ℂ 2 (volume : Measure (ℝ^n × ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ^n) :=
  (frequencyLiftLI n hs).toContinuousLinearMap.adjoint

theorem norm_frequencyRestriction_le (n : ℕ) (hs : 1 / 2 < s) :
    ‖frequencyRestriction n hs‖ ≤ 1 := by
  rw [frequencyRestriction, ContinuousLinearMap.adjoint.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map, one_mul, le_refl]

theorem norm_frequencyRestriction_apply_le (n : ℕ) (hs : 1 / 2 < s)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) :
    ‖frequencyRestriction n hs u‖ ≤ ‖u‖ :=
  ((frequencyRestriction n hs).le_opNorm u).trans
    (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (norm_frequencyRestriction_le n hs) (norm_nonneg u))

theorem frequencyRestriction_frequencyLift (n : ℕ) (hs : 1 / 2 < s)
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    frequencyRestriction n hs (frequencyLift hs v) = v :=
  congr($(LinearIsometry.adjoint_comp_self (frequencyLiftLI n hs)) v)

theorem inner_frequencyRestriction (n : ℕ) (hs : 1 / 2 < s)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    ⟪v, frequencyRestriction n hs u⟫_ℂ = ⟪frequencyLift hs v, u⟫_ℂ :=
  (frequencyLiftLI n hs).toContinuousLinearMap.adjoint_inner_right v u

/-- The concrete kernel integral on a normal-frequency line. -/
def frequencyRestrictionFun (s : ℝ)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) (ξ : ℝ^n) : ℂ :=
  ∫ t : ℝ, frequencyKernel s ξ t • u (ξ, t)

/-- The integral representing restriction is absolutely convergent almost everywhere. -/
theorem ae_integrable_frequencyRestriction (hs : 1 / 2 < s)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) :
    ∀ᵐ ξ ∂volume, Integrable (fun t : ℝ ↦ frequencyKernel s ξ t • u (ξ, t)) := by
  filter_upwards [ae_memLp_normalSlice u] with ξ hξ
  exact integrable_frequencyKernel_smul hs ξ hξ

private theorem aestronglyMeasurable_frequencyRestrictionFun
    (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) :
    AEStronglyMeasurable (frequencyRestrictionFun s u) volume := by
  have hu : AEStronglyMeasurable u (volume.prod volume) := Lp.aestronglyMeasurable u
  exact ((measurable_frequencyKernel s).aestronglyMeasurable.smul hu).integral_prod_right'

theorem memLp_frequencyRestrictionFun (hs : 1 / 2 < s)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) :
    MemLp (frequencyRestrictionFun s u) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_frequencyRestrictionFun u)).2
  have hi : Integrable (fun z ↦ ‖u z‖ ^ 2) (volume.prod volume) :=
    (Lp.memLp u).norm.integrable_sq
  apply hi.integral_prod_left.mono_nonneg
    (aestronglyMeasurable_frequencyRestrictionFun u |>.norm.pow 2)
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
  filter_upwards [ae_memLp_normalSlice u] with ξ hξ
  exact norm_integral_frequencyKernel_smul_sq_le hs ξ hξ

private theorem inner_frequencyLiftFun (v : Lp ℂ 2 (volume : Measure ℝ^n))
    (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) (z : ℝ^n × ℝ) :
    ⟪frequencyLiftFun s v z, u z⟫_ℂ = ⟪v z.1, frequencyKernel s z.1 z.2 • u z⟫_ℂ := by
  simp [frequencyLiftFun, RCLike.inner_apply, Complex.real_smul,
    mul_left_comm, mul_comm, mul_assoc]

/-- The Hilbert adjoint is the normal-frequency integral in `L²`. -/
theorem frequencyRestriction_eq_toLp (hs : 1 / 2 < s)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) :
    frequencyRestriction n hs u =
      (memLp_frequencyRestrictionFun hs u).toLp (frequencyRestrictionFun s u) := by
  apply ext_inner_left ℂ
  intro v
  rw [inner_frequencyRestriction, L2.inner_def, L2.inner_def]
  have hlift := frequencyLift_apply_ae hs v
  have hprod : Integrable
      (fun z : ℝ^n × ℝ ↦ ⟪v z.1, frequencyKernel s z.1 z.2 • u z⟫_ℂ)
      (volume.prod volume) := by
    have h := L2.integrable_inner (𝕜 := ℂ) (frequencyLift hs v) u
    rw [← Measure.volume_eq_prod]
    apply h.congr
    filter_upwards [hlift] with z hz
    rw [hz, inner_frequencyLiftFun]
  calc
    _ = ∫ z : ℝ^n × ℝ, ⟪v z.1, frequencyKernel s z.1 z.2 • u z⟫_ℂ := by
      apply integral_congr_ae
      filter_upwards [hlift] with z hz
      rw [hz, inner_frequencyLiftFun]
    _ = ∫ ξ : ℝ^n, ∫ t : ℝ, ⟪v ξ, frequencyKernel s ξ t • u (ξ, t)⟫_ℂ :=
      integral_prod _ hprod
    _ = ∫ ξ : ℝ^n, ⟪v ξ, frequencyRestrictionFun s u ξ⟫_ℂ := by
      apply integral_congr_ae
      filter_upwards [ae_memLp_normalSlice u] with ξ hξ
      exact integral_inner (integrable_frequencyKernel_smul hs ξ hξ) _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_frequencyRestrictionFun hs u).coeFn_toLp] with ξ hξ
      rw [hξ]

theorem frequencyRestriction_apply_ae (hs : 1 / 2 < s)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) :
    frequencyRestriction n hs u =ᵐ[volume] frequencyRestrictionFun s u := by
  rw [frequencyRestriction_eq_toLp]
  exact (memLp_frequencyRestrictionFun hs u).coeFn_toLp

end SobolevSpace.Fractional.Trace.GeneralOrder
