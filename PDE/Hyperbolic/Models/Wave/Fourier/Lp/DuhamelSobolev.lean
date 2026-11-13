/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.RealL2.Minkowski
public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.Duhamel
public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.SineSobolev

/-!
# Uniform Sobolev bound for physical Duhamel evolution

Real projection commutes with the L2-valued Bochner integral. Minkowski
and the physical sine Sobolev estimate then control every critical finite
spatial exponent by the L1L2 norm of the forcing, at every time. Integrability
of the causal sine curve and its joint representatives are derived internally.
-/

@[expose] public section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal

namespace WaveEquation.Fourier

/-- Minkowski applies to the physical Duhamel integral at every finite
spatial exponent at least one. No spatial Lq integrability is assumed. -/
theorem eLpNorm_re_duhamelL2_le_lintegral {n : ℕ} {q : ℝ} (hq : 1 ≤ q) (a b t : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^n))) 1 (volume.restrict (Icc a b))) :
    eLpNorm (fun x ↦ (duhamelL2 a b t f x).re) (ENNReal.ofReal q) volume ≤ ∫⁻ s in Icc a b,
      eLpNorm (fun x ↦ (sineEvolution (max (t - s) 0) (f s) x).re) (ENNReal.ofReal q) volume := by
  let R : Lp ℂ 2 (volume : Measure (ℝ^n)) →L[ℝ] Lp ℝ 2 volume := Complex.reCLM.compLpL 2 volume
  let v : ℝ → Lp ℂ 2 (volume : Measure (ℝ^n)) := fun s ↦ sineEvolution (max (t - s) 0) (f s)
  have hvi : Integrable v (volume.restrict (Icc a b)) :=
    integrable_causalSineEvolution (L1.integrable_coeFn f) t
  have hRe : (fun x ↦ (duhamelL2 a b t f x).re) =ᵐ[volume]
      (∫ s in Icc a b, R (v s) : Lp ℝ 2 volume) := by
    rw [R.integral_comp_comm hvi]
    change (fun x ↦ (duhamelL2 a b t f x).re) =ᵐ[volume]
      R (∫ s in Icc a b, sineEvolution (max (t - s) 0) (f s))
    rw [← duhamelL2_apply]
    exact Filter.EventuallyEq.symm (Complex.reCLM.coeFn_compLp (duhamelL2 a b t f))
  rw [eLpNorm_congr_ae hRe]
  have hM := Lp.eLpNorm_integral_le_lintegral_eLpNorm (R.integrable_comp hvi) (q := q) hq
  apply hM.trans_eq
  exact lintegral_congr fun s ↦ eLpNorm_congr_ae (Complex.reCLM.coeFn_compLp (v s))

/-- Physical Duhamel has the uniform homogeneous Sobolev norm controlled solely
by L1L2 forcing. The conclusion holds at every time, including both endpoints. -/
theorem eLpNorm_re_duhamelL2_le {n : ℕ} {q : NNReal} (hn : 0 < n)
    (hq : (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (n : ℝ)⁻¹) (hq1 : 1 ≤ q) (a b t : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^n))) 1 (volume.restrict (Icc a b))) :
    eLpNorm (fun x ↦ (duhamelL2 a b t f x).re) q volume ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^n)) 2 : ℝ≥0∞) * n * ‖f‖ₑ := by
  have hM := eLpNorm_re_duhamelL2_le_lintegral (q := (q : ℝ))
    (by exact_mod_cast hq1) a b t f
  rw [ENNReal.ofReal_coe_nnreal] at hM
  apply hM.trans
  calc
    _ ≤ ∫⁻ s in Icc a b,
        (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^n)) 2 : ℝ≥0∞) * n * ‖f s‖ₑ :=
      lintegral_mono fun s ↦ eLpNorm_re_sineEvolution_le hn hq (max (t - s) 0) (f s)
    _ = _ := by
      rw [lintegral_const_mul'' _ (Lp.aestronglyMeasurable f).enorm,
        ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f), ← Lp.enorm_def]

end WaveEquation.Fourier
