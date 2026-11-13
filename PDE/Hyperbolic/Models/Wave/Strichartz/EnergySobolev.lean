/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.SineWeakGradient
public import PDE.Hyperbolic.Models.Wave.Strichartz.InitialEnergy
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.Weak

/-!
# Uniform Sobolev bound for the physical homogeneous wave

The Fourier multipliers of spatial derivatives are controlled by exactly one
frequency weight on displacement and no weight on velocity. Plancherel and the
weak Sobolev inequality therefore bound the real part of the physical Schwartz
wave in L6 at every time. No displacement L2 norm appears on the right.
-/

@[expose] public section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal SchwartzMap

namespace WaveEquation.Fourier

/-- The coordinate derivative of the wave multiplier is bounded by
one frequency weight on displacement and no frequency weight on velocity. -/
theorem norm_coordinate_mul_waveValue_le {n : ℕ} (i : Fin n) (ξ : ℝ^n) (t : ℝ) (G H : ℂ) :
    ‖((2 * Real.pi * Complex.I) * (ξ i : ℂ)) * waveValue (2 * Real.pi * ‖ξ‖) G H t‖ ≤
      (2 * Real.pi * ‖ξ‖) * ‖G‖ + ‖H‖ := by
  let m : ℂ := (2 * Real.pi * Complex.I) * (ξ i : ℂ)
  have hm : ‖m‖ ≤ 2 * Real.pi * ‖ξ‖ := by
    dsimp only [m]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
      Real.norm_of_nonneg Real.pi_pos.le, mul_one, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le ξ i) (by positivity)
  change ‖m * (_ + _)‖ ≤ _
  rw [mul_add]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg G) (Real.abs_cos_le_one _)) (norm_nonneg m)).trans
      (mul_le_mul_of_nonneg_right hm (norm_nonneg G))
  · rw [norm_mul, norm_smul, Real.norm_eq_abs, ← mul_assoc]
    exact mul_le_of_le_one_left (norm_nonneg H) (norm_coordinate_mul_sineKernel_le i ξ t)

end WaveEquation.Fourier

namespace WaveEquation.Strichartz

open WaveEquation.Fourier

/-- The Schwartz Fourier wave satisfies the uniform spatial L6 bound
with exactly derivative displacement energy and velocity energy. -/
theorem eLpNorm_re_waveSolution_six_le (g h : 𝓢(ℝ^3, ℂ)) (t : ℝ) :
    eLpNorm (fun x ↦ (waveSolution (𝓕 g : 𝓢(ℝ^3, ℂ)) (𝓕 h : 𝓢(ℝ^3, ℂ)) (t, x)).re)
      6 volume ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^3)) 2 : ℝ≥0∞) * 3 *
        (‖(initialEnergyDatum g h).fst‖ₑ + ‖(initialEnergyDatum g h).snd‖ₑ) := by
  classical
  let G := (𝓕 g : 𝓢(ℝ^3, ℂ))
  let H := (𝓕 h : 𝓢(ℝ^3, ℂ))
  let k : ℝ^3 → ℂ := fun ξ ↦ waveValue (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) t
  have hk : MemLp k 2 volume := by
    apply ((G.memLp 2 volume).norm.add ((H.memLp 2 volume).norm.const_mul |t|)).of_le
      (by dsimp only [k, waveValue, sineKernel]; fun_prop)
    filter_upwards with ξ
    change ‖k ξ‖ ≤ ‖‖G ξ‖ + |t| * ‖H ξ‖‖
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖G ξ‖ + |t| * ‖H ξ‖)]
    exact norm_waveValue_le _ _ _ _ _ le_rfl
  let z : Lp ℂ 2 (volume : Measure (ℝ^3)) := 𝓕⁻ (hk.toLp k)
  have hphysical : (fun x ↦ waveSolution G H (t, x)) =ᵐ[volume] z :=
    PDE.Analysis.Fourier.fourierInvIntegral_eq_L2_ae
      (integrable_waveValue G H t) _ hk.coeFn_toLp.symm
  let U := (initialEnergyDatum g h).fst
  let V := (initialEnergyDatum g h).snd
  let B : ℝ^3 → ℝ := fun ξ ↦ ‖U ξ‖ + ‖V ξ‖
  have hB : MemLp B 2 volume := (Lp.memLp U).norm.add (Lp.memLp V).norm
  have hderiv (i : Fin 3) : ∃ v : Lp ℂ 2 (volume : Measure (ℝ^3)),
      SobolevSpace.HasComplexWeakDerivativeOn univ [i] z v ∧
        eLpNorm (fun x ↦ (v x).re) 2 volume ≤ ‖U‖ₑ + ‖V‖ₑ := by
    let m : ℝ^3 → ℂ := fun ξ ↦ (2 * Real.pi * Complex.I) * (ξ i : ℂ) * k ξ
    have hb : ∀ᵐ ξ ∂volume, ‖m ξ‖ ≤ ‖B ξ‖ := by
      filter_upwards [initialEnergyDatum_fst_ae_eq g h, initialEnergyDatum_snd_ae_eq g h]
        with ξ hU hV
      change ‖m ξ‖ ≤ ‖‖(initialEnergyDatum g h).fst ξ‖ + ‖(initialEnergyDatum g h).snd ξ‖‖
      rw [hU, hV, Real.norm_of_nonneg (by positivity), norm_smul,
        Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * ‖ξ‖)]
      exact norm_coordinate_mul_waveValue_le i ξ t (G ξ) (H ξ)
    have hm : MemLp m 2 volume := hB.of_le (by
      dsimp only [m, k, waveValue, sineKernel]
      fun_prop) hb
    let v : Lp ℂ 2 (volume : Measure (ℝ^3)) := 𝓕⁻ (hm.toLp m)
    refine ⟨v, ?_, ?_⟩
    · apply (SobolevSpace.hasComplexWeakDerivativeOn_iff_fourier [i] z v).mpr
      change (fun ξ ↦ (∏ j : Fin 1, (2 * Real.pi * Complex.I) * (ξ ([i].get j) : ℂ)) *
        (𝓕 (𝓕⁻ (hk.toLp k)) : Lp ℂ 2 volume) ξ) =ᵐ[volume] (𝓕 (𝓕⁻ (hm.toLp m)) : Lp ℂ 2 volume)
      simp only [Fin.prod_univ_one, List.get_cons_zero, fourier_fourierInv_eq]
      filter_upwards [hk.coeFn_toLp, hm.coeFn_toLp] with ξ hξ hmξ
      rw [hξ, hmξ]
    · calc
        _ ≤ eLpNorm v 2 volume := eLpNorm_mono_ae
          (Complex.continuous_re.comp_aestronglyMeasurable (Lp.aestronglyMeasurable v))
          (Filter.Eventually.of_forall fun x ↦ by
            simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (v x))
        _ = eLpNorm m 2 volume := by
          rw [← Lp.enorm_def, ← Lp.enorm_toLp (f := m) (hf := hm)]
          have he : ‖v‖ = ‖hm.toLp m‖ := by
            simpa only [v, fourier_fourierInv_eq] using (Lp.norm_fourier_eq v).symm
          simpa only [ofReal_norm] using congrArg ENNReal.ofReal he
        _ ≤ eLpNorm B 2 volume := eLpNorm_mono_ae hm.aestronglyMeasurable hb
        _ ≤ _ := by
          calc
            _ ≤ eLpNorm (fun ξ ↦ ‖U ξ‖) 2 volume + eLpNorm (fun ξ ↦ ‖V ξ‖) 2 volume :=
              eLpNorm_add_le (by norm_num)
            _ = _ := by
              rw [eLpNorm_norm U (Lp.aestronglyMeasurable U),
                eLpNorm_norm V (Lp.aestronglyMeasurable V), ← Lp.enorm_def, ← Lp.enorm_def]
  choose v hv hb using hderiv
  apply le_trans (le_of_eq (eLpNorm_congr_ae (p := 6) (hphysical.fun_comp Complex.re)))
  have hs := SobolevSpace.Inequalities.eLpNorm_le_sum_eLpNorm_weakDeriv
    (p := (2 : NNReal)) (q := (6 : NNReal)) (by norm_num) (by norm_num : 0 < 3)
    (by norm_num) (Lp.memLp z).re (fun i ↦ (Lp.memLp (v i)).re) (fun i ↦ (hv i).1)
  apply hs.trans
  calc
    _ ≤ (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^3)) 2 : ℝ≥0∞) *
        ∑ _i : Fin 3, (‖U‖ₑ + ‖V‖ₑ) := mul_le_mul_right (Finset.sum_le_sum fun i _ ↦ hb i) _
    _ = _ := by simp [mul_assoc, mul_add, U, V]

end WaveEquation.Strichartz
