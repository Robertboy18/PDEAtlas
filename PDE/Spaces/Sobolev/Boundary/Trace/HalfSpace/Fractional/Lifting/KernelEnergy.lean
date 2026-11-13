/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.KernelEnergy.Field
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.DisplacementEnergy
public import PDE.Spaces.Sobolev.Approximation.Mollification.ScaleDerivative.Cancellation

/-!
# Fractional norm bounds for signed kernel fields

For `p > 1`, a continuous compactly supported zero-mean kernel sends boundary
Banach-valued data of order `1 - 1/p` to an `Lᵖ` field on the upper half-space. The
signed-kernel height estimate and the displacement identity give the bound
directly from the Gagliardo graph norm.

The result applies to both derivative profiles of every mollifier. A support
radius is chosen from compactness; a fixed radius is not assumed for a general
mollifier. All statements include dimension zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Trace.HalfSpace

open Fractional

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A support radius and kernel bound give an explicit `Lᵖ` norm estimate. -/
theorem eLpNorm_signedKernelField_le {R M : ℝ} (hp : 1 < p) (hR : 0 < R)
    {ψ : ℝ^n → ℝ} (hψ : Continuous ψ)
    (hψsupport : Function.support ψ ⊆ Metric.ball 0 R)
    (hψbound : ∀ y, |ψ y| ≤ M) (hψzero : ∫ y, ψ y = 0)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F)) :
    eLpNorm (signedKernelField ψ (GagliardoSpace.toLp n (1 - 1 / p) univ g))
        (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊) ≤
      ENNReal.ofReal (((volume.real (Metric.ball (0 : ℝ^n) R)) ^ (p - 1) * M ^ p *
        (R ^ ((n : ℝ) + p - 1) / ((n : ℝ) + p - 1))) ^ (1 / p)) * ‖g‖ₑ := by
  have hp₀ : 0 < p := zero_lt_one.trans hp
  have hq : 0 < (n : ℝ) + p - 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hM : 0 ≤ M := (abs_nonneg (ψ 0)).trans (hψbound 0)
  let A := (volume.real (Metric.ball (0 : ℝ^n) R)) ^ (p - 1) * M ^ p *
    (R ^ ((n : ℝ) + p - 1) / ((n : ℝ) + p - 1))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hg : MemLp (GagliardoSpace.toLp n (1 - 1 / p) univ g)
      (ENNReal.ofReal p) volume := by
    simpa only [Measure.restrict_univ] using
      Lp.memLp (GagliardoSpace.toLp n (1 - 1 / p) univ g)
  have hgm := Lp.stronglyMeasurable (GagliardoSpace.toLp n (1 - 1 / p) univ g)
  have hdisp := GagliardoSpace.lintegral_weighted_displacement_le g
  simp only [sub_mul, one_mul, one_div, inv_mul_cancel₀ hp₀.ne',
    ← add_sub_assoc] at hdisp
  have henergy :
      (∫⁻ z in ℝ^(n + 1)₊,
        ENNReal.ofReal (‖signedKernelField ψ
          (GagliardoSpace.toLp n (1 - 1 / p) univ g) z‖ ^ p)) ≤
        ENNReal.ofReal A * ‖g‖ₑ ^ p :=
    (lintegral_signedKernelField_rpow_le hp hR hψ hψsupport hψbound hψzero hg hgm).trans
      (mul_le_mul' le_rfl hdisp)
  have hm := (stronglyMeasurable_signedKernelField hψ.measurable hgm).aestronglyMeasurable
    (μ := volume.restrict ℝ^(n + 1)₊)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp₀).ne'
    ENNReal.ofReal_ne_top hm, ENNReal.toReal_ofReal hp₀.le]
  simp_rw [← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp₀.le]
  calc
    _ ≤ (ENNReal.ofReal A * ‖g‖ₑ ^ p) ^ (1 / p) :=
      ENNReal.rpow_le_rpow henergy (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ENNReal.ofReal_rpow_of_nonneg hA (by positivity)]
      simp only [A, one_div, ENNReal.rpow_rpow_inv hp₀.ne', ofReal_norm]

/-- A compact zero-mean kernel has one positive norm bound valid for all boundary data. -/
theorem exists_pos_signedKernelField_bound (hp : 1 < p) {ψ : ℝ^n → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψzero : ∫ y, ψ y = 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F),
        MemLp (signedKernelField ψ (GagliardoSpace.toLp n (1 - 1 / p) univ g))
            (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊) ∧
          eLpNorm (signedKernelField ψ (GagliardoSpace.toLp n (1 - 1 / p) univ g))
            (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊) ≤ ENNReal.ofReal C * ‖g‖ₑ := by
  obtain ⟨R, hR, hs⟩ := hψc.isBounded.subset_ball_lt 0 (0 : ℝ^n)
  obtain ⟨M, hM⟩ := hψc.exists_bound_of_continuous hψ
  let C := ((volume.real (Metric.ball (0 : ℝ^n) R)) ^ (p - 1) * M ^ p *
    (R ^ ((n : ℝ) + p - 1) / ((n : ℝ) + p - 1))) ^ (1 / p)
  have hC : 0 ≤ C := Real.rpow_nonneg (by
    have hq : 0 < (n : ℝ) + p - 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hM₀ : 0 ≤ M := (norm_nonneg (ψ 0)).trans (hM 0)
    positivity) _
  refine ⟨C + 1, by positivity, fun g ↦ ?_⟩
  have hb := eLpNorm_signedKernelField_le hp hR hψ ((subset_tsupport ψ).trans hs)
    (by simpa only [Real.norm_eq_abs] using hM) hψzero g
  have hb' : eLpNorm (signedKernelField ψ (GagliardoSpace.toLp n (1 - 1 / p) univ g))
      (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊) ≤ ENNReal.ofReal (C + 1) * ‖g‖ₑ :=
    hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)) le_rfl)
  exact ⟨hb'.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top), hb'⟩

/-- Fractional boundary data give an `Lᵖ` signed kernel field. -/
theorem memLp_signedKernelField (hp : 1 < p) {ψ : ℝ^n → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψzero : ∫ y, ψ y = 0)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F)) :
    MemLp (signedKernelField ψ (GagliardoSpace.toLp n (1 - 1 / p) univ g))
      (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊) := by
  obtain ⟨_, _, hb⟩ := exists_pos_signedKernelField_bound (F := F) hp hψ hψc hψzero
  exact (hb g).1

/-- The `Lp` class of the signed field is uniformly bounded by the boundary norm. -/
theorem exists_pos_norm_signedKernelField_bound (hp : 1 < p) {ψ : ℝ^n → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψzero : ∫ y, ψ y = 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F),
        ‖((memLp_signedKernelField hp hψ hψc hψzero g).toLp
          (signedKernelField ψ (GagliardoSpace.toLp n (1 - 1 / p) univ g)) :
            Lp F (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊))‖ ≤ C * ‖g‖ := by
  obtain ⟨C, hC, hb⟩ := exists_pos_signedKernelField_bound (F := F) hp hψ hψc hψzero
  refine ⟨C, hC, fun g ↦ ?_⟩
  rw [Lp.norm_toLp]
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top) (hb g).2
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le, toReal_enorm] using h

/-- The spatial derivative profile of any mollifier has the fractional norm bound. -/
theorem exists_pos_spatialDerivativeProfile_bound (hp : 1 < p)
    (μ : Approximation.Mollifier n) (i : Fin n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F),
        MemLp (signedKernelField (μ.spatialDerivativeProfile i)
            (GagliardoSpace.toLp n (1 - 1 / p) univ g))
            (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊) ∧
          eLpNorm (signedKernelField (μ.spatialDerivativeProfile i)
            (GagliardoSpace.toLp n (1 - 1 / p) univ g))
            (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊) ≤ ENNReal.ofReal C * ‖g‖ₑ :=
  exists_pos_signedKernelField_bound hp (μ.contDiff_spatialDerivativeProfile i).continuous
    (μ.hasCompactSupport_spatialDerivativeProfile i) (μ.integral_spatialDerivativeProfile i)

/-- The normal derivative profile of any mollifier has the fractional norm bound. -/
theorem exists_pos_normalDerivativeProfile_bound (hp : 1 < p)
    (μ : Approximation.Mollifier n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F),
        MemLp (signedKernelField μ.normalDerivativeProfile
            (GagliardoSpace.toLp n (1 - 1 / p) univ g))
            (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊) ∧
          eLpNorm (signedKernelField μ.normalDerivativeProfile
            (GagliardoSpace.toLp n (1 - 1 / p) univ g))
            (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊) ≤ ENNReal.ofReal C * ‖g‖ₑ :=
  exists_pos_signedKernelField_bound hp μ.contDiff_normalDerivativeProfile.continuous
    μ.hasCompactSupport_normalDerivativeProfile μ.integral_normalDerivativeProfile

end SobolevSpace.Trace.HalfSpace
