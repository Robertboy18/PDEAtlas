/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Sobolev

/-!
# Integrable Fourier moments of Sobolev data

If `s > dim(E) / 2 + r`, a Sobolev distribution of order `s` has a single
integrable Fourier representative whose frequency moments through order `r` are
integrable. The order `s` is real and need not be an integer.

The proof applies Mathlib's Sobolev-to-`L¹` Fourier estimate to the Bessel
potential of order `r`. Multiplication by the inverse Bessel weight then recovers
the original distribution. Each required frequency moment is bounded by the
integrable representative of the shifted datum.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal NNReal

namespace PDE.Analysis.Fourier

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- An inverse Bessel weight absorbs all norm powers up to its order, including
at zero frequency. -/
private theorem norm_pow_mul_bessel_weight_le_one (ξ : E) {k r : ℕ} (hkr : k ≤ r) :
    ‖ξ‖ ^ k * (1 + ‖ξ‖ ^ 2) ^ (-(r : ℝ) / 2) ≤ 1 := by
  have hbase : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hpow : ‖ξ‖ ^ k ≤ (1 + ‖ξ‖ ^ 2) ^ ((r : ℝ) / 2) := by
    calc
      ‖ξ‖ ^ k = (‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) := by
        rw [← Real.rpow_natCast ‖ξ‖ 2, ← Real.rpow_mul (norm_nonneg ξ)]
        simp only [Nat.cast_ofNat]
        rw [show (2 : ℝ) * ((k : ℝ) / 2) = k by ring, Real.rpow_natCast]
      _ ≤ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) :=
        Real.rpow_le_rpow (sq_nonneg _) (by linarith) (by positivity)
      _ ≤ (1 + ‖ξ‖ ^ 2) ^ ((r : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg _))
          (div_le_div_of_nonneg_right (by exact_mod_cast hkr) (by positivity))
  calc
    ‖ξ‖ ^ k * (1 + ‖ξ‖ ^ 2) ^ (-(r : ℝ) / 2) ≤
        (1 + ‖ξ‖ ^ 2) ^ ((r : ℝ) / 2) *
          (1 + ‖ξ‖ ^ 2) ^ (-(r : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hbase.le _)
    _ = 1 := by
      rw [← Real.rpow_add hbase, neg_div, add_neg_cancel, Real.rpow_zero]

/-- Sobolev regularity above `dim(E)/2 + r` produces an `L¹` Fourier
representative with every frequency moment through order `r` integrable.
No moment bound or integral representation is assumed. -/
theorem exists_fourier_memL1_moments_of_memSobolev {s : ℝ} {r : ℕ}
    (hs : (Module.finrank ℝ E : ℝ) < 2 * (s - r))
    {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
    ∃ g : Lp F 1 (volume : Measure E), 𝓕 f = (g : 𝓢'(E, F)) ∧
      ∀ k ≤ r, Integrable (fun ξ : E ↦ ‖ξ‖ ^ k * ‖g ξ‖) := by
  have hshift : MemSobolev (s - r) 2 (besselPotential E F r f) := by
    rw [memSobolev_besselPotential_iff]
    convert hf using 1
    ring
  obtain ⟨v, hv⟩ := hshift.fourier_memL1 hs
  let w : E → ℂ := fun ξ ↦ ↑((1 + ‖ξ‖ ^ 2) ^ (-(r : ℝ) / 2) : ℝ)
  have hw : w.HasTemperateGrowth := by
    dsimp only [w]
    fun_prop
  have hwinf : MemLp w ∞ (volume : Measure E) := by
    refine memLp_top_of_bound hw.1.continuous.aestronglyMeasurable 1 ?_
    filter_upwards with ξ
    dsimp only [w]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (sq_nonneg _))
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg r)) (by positivity))
  let g : Lp F 1 (volume : Measure E) := hwinf.toLp w • v
  have hg : 𝓕 f = (g : 𝓢'(E, F)) := by
    dsimp only [g]
    rw [Lp.toTemperedDistribution_smul_eq hw hwinf, ← hv,
      fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      smulLeftCLM_smulLeftCLM_apply (by fun_prop) hw]
    convert! (smulLeftCLM_const 1 (𝓕 f)).symm using 1
    · simp
    · congr
      ext ξ
      change (↑((1 + ‖ξ‖ ^ 2) ^ ((r : ℝ) / 2) : ℝ) : ℂ) *
        ↑((1 + ‖ξ‖ ^ 2) ^ (-(r : ℝ) / 2) : ℝ) = 1
      rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity), neg_div, add_neg_cancel,
        Real.rpow_zero, Complex.ofReal_one]
  refine ⟨g, hg, fun k hk ↦ ?_⟩
  have hgmeas : AEStronglyMeasurable (fun ξ : E ↦ ‖ξ‖ ^ k * ‖g ξ‖) volume :=
    (continuous_norm.pow k).aestronglyMeasurable.mul (Lp.aestronglyMeasurable g).norm
  refine (L1.integrable_coeFn v).norm.mono' hgmeas ?_
  filter_upwards [Lp.coeFn_lpSMul (r := 1) (hwinf.toLp w) v,
    hwinf.coeFn_toLp] with ξ hprod hwξ
  change ‖‖ξ‖ ^ k * ‖(hwinf.toLp w • v : Lp F 1 volume) ξ‖‖ ≤ ‖v ξ‖
  rw [hprod, Pi.smul_apply', hwξ, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  dsimp only [w]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right
    (norm_pow_mul_bessel_weight_le_one ξ hk) (norm_nonneg _)).trans_eq (one_mul _)

end PDE.Analysis.Fourier
