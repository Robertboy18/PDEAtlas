/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import PDE.Hyperbolic.Models.Wave.Strichartz.Classical
public import PDE.Hyperbolic.Models.Wave.Strichartz.ClassicalSobolev
public import PDE.Hyperbolic.Models.Wave.Strichartz.InitialEnergyNorm

/-!
# The three-dimensional classical wave estimate

The closed-time supremum of the spatial L6 norm and the mixed L4L12 norm are
bounded by the physical gradient and velocity L2 norms and real L1L2 forcing.
The constant is independent of the time interval. Real forcing is transported
through Mathlib's bounded maps on Bochner spaces with explicit AE identities.

This gives the estimate (4) of Evans, §12.4, Theorem 1, for Schwartz initial data, which include the
compactly supported smooth data assumed throughout §12.4. Evans allows the constant to depend on
`T`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 1, equations (3)-(4), and step 2 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory FourierTransform Filter Set PDE PDE.Common
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

/-- The classical three-dimensional wave satisfies the closed-time uniform L6
and mixed L4L12 estimates with the conventional physical initial-data norms. -/
theorem classicalWave_estimate {b : ℝ} (hb : 0 < b) (g h : 𝓢(ℝ^3, ℝ))
    (f : Lp (Lp ℝ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc 0 b))) {u U U₂ : ℝ → ℝ^3 → ℝ}
    (hu : ContinuousOn u.uncurry (Icc 0 b ×ˢ univ)) (hU : ContinuousOn U.uncurry (Icc 0 b ×ˢ univ))
    (hU₂ : ContinuousOn U₂.uncurry (Ioo 0 b ×ˢ univ))
    (hdu : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ u r x) (U s x) s)
    (hdU : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ U r x) (U₂ s x) s)
    (hu₂ : ∀ s ∈ Ioo 0 b, ContDiff ℝ 2 (u s)) (hpos : ∀ x, u 0 x = g x) (hvel : ∀ x, U 0 x = h x)
    (hr : ∀ᵐ s ∂volume.restrict (Icc 0 b), (f s : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦
      (U₂ s x - laplacian (u s) x)) :
    (⨆ t : Icc 0 b, lpNorm (u t) 6 volume) +
      lpNorm (fun t ↦ lpNorm (u t) 12 volume) 4 (volume.restrict (Ioo 0 b)) ≤
        ((SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^3)) 2 : ℝ) * 6 +
          energyAdjointBound) *
            (lpNorm (fderiv ℝ g) 2 volume + lpNorm h 2 volume + ‖f‖) := by
  let μ := volume.restrict (Icc 0 b)
  let C : Lp ℝ 2 (volume : Measure (ℝ^3)) →L[ℝ] Lp ℂ 2 volume := Complex.ofRealCLM.compLpL 2 volume
  let fc : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 μ := C.compLpL 1 μ f
  have hC : ‖C‖ ≤ 1 := by
    simpa only [C, Complex.ofRealCLM, LinearIsometry.norm_toContinuousLinearMap] using
      (Complex.ofRealCLM.norm_compLpL_le (p := 2) (μ := (volume : Measure (ℝ^3))))
  have hfc : ‖fc‖ ≤ ‖f‖ := (C.norm_compLp_le f).trans
    ((mul_le_mul_of_nonneg_right hC (norm_nonneg f)).trans_eq (one_mul _))
  have hrc : ∀ᵐ s ∂μ, (fc s : ℝ^3 → ℂ) =ᵐ[volume]
      fun x ↦ ((U₂ s x - laplacian (u s) x : ℝ) : ℂ) := by
    filter_upwards [hr, C.coeFn_compLpL f] with t ht hct
    change fc t = C (f t) at hct
    rw [hct]
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL (f t), ht] with x hx hrx
    simpa only [Complex.ofRealCLM_apply, hrx] using hx
  let d := initialEnergyDatum (g.postcompCLM Complex.ofRealCLM) (h.postcompCLM Complex.ofRealCLM)
  let B := lpNorm (fderiv ℝ g) 2 volume + lpNorm h 2 volume + ‖f‖
  have hdata : ‖d‖ + ‖fc‖ ≤ B := add_le_add (norm_initialEnergyDatum_real_le g h) hfc
  let S : NNReal := SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^3)) 2
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 b) : lpNorm (u t) 6 volume ≤ (S : ℝ) * 6 * B := by
    have h6 := eLpNorm_classicalWave_six_le g h fc hu hU hU₂ hdu hdU hu₂ hpos hvel hrc t ht
    have hfinit : (S : ℝ≥0∞) * 6 * (‖d‖ₑ + ‖fc‖ₑ) ≠ ∞ := by finiteness
    have hreal := ENNReal.toReal_mono hfinit h6
    simp only [toReal_eLpNorm, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofNat, ENNReal.toReal_add enorm_ne_top enorm_ne_top, toReal_enorm] at hreal
    exact hreal.trans (mul_le_mul_of_nonneg_left hdata (by positivity))
  have h4 := eLpNorm_classicalWave_le g h fc hu hU hU₂ hdu hdU hu₂ hpos hvel hrc
  have hM : MemLp (fun t ↦ eLpNorm (u t) 12 volume) 4 μ := lt_of_le_of_lt h4 ENNReal.ofReal_lt_top
  have hnorm : eLpNorm (fun t ↦ lpNorm (u t) 12 volume) 4 μ =
      eLpNorm (fun t ↦ eLpNorm (u t) 12 volume) 4 μ := by
    apply eLpNorm_congr_enorm_ae
      hM.aestronglyMeasurable.aemeasurable.ennreal_toReal.aestronglyMeasurable
      hM.aestronglyMeasurable
    filter_upwards [hM.ae_lt_top (by norm_num) (by norm_num)] with t ht
    exact (Real.enorm_toReal ht.ne).trans (enorm_eq_self _).symm
  have hE : 0 ≤ energyAdjointBound := Real.sqrt_nonneg _
  have h4real : lpNorm (fun t ↦ lpNorm (u t) 12 volume) 4 μ ≤
      energyAdjointBound * B := by
    have hbound := ENNReal.toReal_mono ENNReal.ofReal_ne_top h4
    rw [← hnorm, toReal_eLpNorm, ENNReal.toReal_ofReal (mul_nonneg hE
      (add_nonneg (norm_nonneg d) (norm_nonneg fc)))] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_left hdata hE)
  have : Nonempty (Icc 0 b) := ⟨⟨0, le_rfl, hb.le⟩⟩
  have hsup : (⨆ t : Icc 0 b, lpNorm (u t) 6 volume) ≤ (S : ℝ) * 6 * B :=
    ciSup_le fun t ↦ hpoint t t.property
  rw [restrict_Ioo_eq_restrict_Icc]
  exact (add_le_add hsup h4real).trans_eq (add_mul _ _ _).symm

end WaveEquation.Strichartz
