/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.L2Multiplier
public import PDE.Spaces.Sobolev.Fractional.Integer.NormComparison
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.FourierWeight

/-!
# Whole-space heat multipliers and one-order Sobolev gain

The actual Gaussian Fourier symbol defines a contraction on L². Multiplication
of the Bessel representative by the reduced symbol
`sqrt(1 + |ξ|²) exp(-4π²t|ξ|²)` gives an operator Hˢ→Hˢ⁺¹ with bound
`1 + (8π²t)^(-1/2)`. Real evenness preserves the real Bessel subspaces.
The low-frequency term is necessary for inhomogeneous Sobolev norms.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform BesselPotentialSpace
open scoped ENNReal NNReal BesselPotentialSpace Real

namespace HeatEquation.WholeSpace

variable {n : ℕ}

/-- The whole-space heat symbol with Mathlib's Fourier normalization. -/
def heatSymbol (n : ℕ) (t : ℝ≥0) (ξ : ℝ^n) : ℂ :=
  (Real.exp (-(4 * π ^ 2 * (t : ℝ) * ‖ξ‖ ^ 2)) : ℝ)

theorem norm_heatSymbol_le_one (t : ℝ≥0) (ξ : ℝ^n) :
    ‖heatSymbol n t ξ‖ ≤ 1 := by
  rw [heatSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))

theorem memLp_top_heatSymbol (t : ℝ≥0) :
    MemLp (heatSymbol n t) ∞ (volume : Measure (ℝ^n)) := by
  refine memLp_top_of_bound
    (by unfold heatSymbol; fun_prop : Continuous (heatSymbol n t)).aestronglyMeasurable 1 ?_
  filter_upwards with ξ using norm_heatSymbol_le_one t ξ

/-- `heatSymbol n t` as an element of `L^∞`, with norm at most `1`. -/
def heatSymbolLinf (n : ℕ) (t : ℝ≥0) : Lp ℂ ∞ (volume : Measure (ℝ^n)) :=
  (memLp_top_heatSymbol (n := n) t).toLp _

theorem norm_heatSymbolLinf_le_one (t : ℝ≥0) : ‖heatSymbolLinf n t‖ ≤ 1 := by
  rw [heatSymbolLinf, Lp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _),
    eLpNorm_exponent_top (memLp_top_heatSymbol (n := n) t).aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_bound
    (by filter_upwards with ξ using norm_heatSymbol_le_one t ξ)

/-- The actual L² heat multiplier. -/
def heatL2 (n : ℕ) (t : ℝ≥0) :
    Lp ℂ 2 (volume : Measure (ℝ^n)) →L[ℂ] Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  PDE.Analysis.Fourier.fourierMultiplierL2 (heatSymbolLinf n t)

theorem norm_heatL2_le (t : ℝ≥0) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    ‖heatL2 n t u‖ ≤ ‖u‖ := by
  exact (PDE.Analysis.Fourier.norm_fourierMultiplierL2_apply_le _ u).trans
    (by simpa using (mul_le_mul_of_nonneg_right
      (norm_heatSymbolLinf_le_one (n := n) t) (norm_nonneg u)))

/-- A scalar Gaussian absorbs a single frequency power. For `r < 0` the left side is
negative. -/
theorem mul_gaussian_le_inv_sqrt {c r : ℝ} (hc : 0 < c) :
    r * Real.exp (-(c * r ^ 2)) ≤ (Real.sqrt (2 * c))⁻¹ := by
  rcases lt_or_ge r 0 with hr | hr
  · exact (mul_neg_of_neg_of_pos hr (Real.exp_pos _)).le.trans
      (inv_nonneg.2 (Real.sqrt_nonneg _))
  have hgauss := Real.mul_exp_neg_le_exp_neg_one (2 * c * r ^ 2)
  have hexp : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hsqexp : (Real.exp (-(c * r ^ 2))) ^ 2 =
      Real.exp (-(2 * c * r ^ 2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : (Real.sqrt (2 * c)) ^ 2 = 2 * c :=
    Real.sq_sqrt (by positivity)
  have hpos : 0 < Real.sqrt (2 * c) := Real.sqrt_pos.2 (by positivity)
  have hprod : Real.sqrt (2 * c) * (r * Real.exp (-(c * r ^ 2))) ≤ 1 := by
    have hbound := hgauss.trans hexp
    rw [← hsqexp] at hbound
    have hprod_sq : (Real.sqrt (2 * c) * (r * Real.exp (-(c * r ^ 2)))) ^ 2 ≤ 1 := by
      calc
        _ = 2 * c * r ^ 2 * (Real.exp (-(c * r ^ 2))) ^ 2 := by
          rw [mul_pow, mul_pow, hsq]
          ring
        _ ≤ 1 := hbound
    have hnonneg : 0 ≤ Real.sqrt (2 * c) * (r * Real.exp (-(c * r ^ 2))) :=
      mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hr (Real.exp_pos _).le)
    nlinarith [sq_nonneg (Real.sqrt (2 * c) * (r * Real.exp (-(c * r ^ 2))) - 1)]
  rw [← one_div]
  exact (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hprod)

/-- The reduced symbol `sqrt(1 + |ξ|²) exp(-4π²t|ξ|²)`: the heat symbol times one Bessel
weight. -/
def gainSymbol (n : ℕ) (t : ℝ) (ξ : ℝ^n) : ℂ :=
  (Real.sqrt (1 + ‖ξ‖ ^ 2) *
    Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ)

/-- `1 + (8π²t)^(-1/2)`, the sup bound on `gainSymbol n t` for `t > 0`. -/
def gainBound (t : ℝ) : ℝ := 1 + (Real.sqrt (8 * π ^ 2 * t))⁻¹

theorem gainBound_nonneg (t : ℝ) : 0 ≤ gainBound t := by
  unfold gainBound
  positivity

theorem norm_gainSymbol_le {t : ℝ} (ht : 0 < t) (ξ : ℝ^n) :
    ‖gainSymbol n t ξ‖ ≤ gainBound t := by
  have hsqrt : Real.sqrt (1 + ‖ξ‖ ^ 2) ≤ 1 + ‖ξ‖ := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 1 + ‖ξ‖ ^ 2),
      Real.sqrt_nonneg (1 + ‖ξ‖ ^ 2), norm_nonneg ξ]
  have hexp : Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hlinear := mul_gaussian_le_inv_sqrt
    (c := 4 * π ^ 2 * t) (r := ‖ξ‖) (by positivity)
  rw [show 2 * (4 * π ^ 2 * t) = 8 * π ^ 2 * t by ring] at hlinear
  rw [gainSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  calc
    _ ≤ (1 + ‖ξ‖) * Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_right hsqrt (Real.exp_pos _).le
    _ = Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) +
        ‖ξ‖ * Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) := by ring
    _ ≤ gainBound t := add_le_add hexp hlinear

theorem memLp_top_gainSymbol {t : ℝ} (ht : 0 < t) :
    MemLp (gainSymbol n t) ∞ (volume : Measure (ℝ^n)) := by
  refine memLp_top_of_bound
    (by unfold gainSymbol; fun_prop : Continuous (gainSymbol n t)).aestronglyMeasurable
      (gainBound t) ?_
  filter_upwards with ξ using norm_gainSymbol_le ht ξ

/-- `gainSymbol n t` as an element of `L^∞`, for `t > 0`, with norm at most `gainBound t`. -/
def gainSymbolLinf (n : ℕ) (t : ℝ) (ht : 0 < t) :
    Lp ℂ ∞ (volume : Measure (ℝ^n)) :=
  (memLp_top_gainSymbol (n := n) ht).toLp _

theorem norm_gainSymbolLinf_le {t : ℝ} (ht : 0 < t) :
    ‖gainSymbolLinf n t ht‖ ≤ gainBound t := by
  rw [gainSymbolLinf, Lp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal (gainBound_nonneg t) ?_
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _),
    eLpNorm_exponent_top (memLp_top_gainSymbol (n := n) ht).aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_bound
    (by filter_upwards with ξ using norm_gainSymbol_le ht ξ)

/-- Exact Bessel-weight factorization, with no differential operator assumed. -/
theorem gainSymbol_factorization (s : ℝ) (t : ℝ≥0) (ξ : ℝ^n) :
    SobolevSpace.Fractional.besselSymbol n (s + 1) ξ * heatSymbol n t ξ =
      gainSymbol n (t : ℝ) ξ * SobolevSpace.Fractional.besselSymbol n s ξ := by
  simp only [SobolevSpace.Fractional.besselSymbol, heatSymbol, gainSymbol,
    ← Complex.ofReal_mul, Complex.ofReal_inj]
  rw [show (s + 1) / 2 = s / 2 + 1 / 2 by ring,
    Real.rpow_add (by positivity), Real.sqrt_eq_rpow]
  ring

private theorem fourierMultiplierL2_isReal
    (m : Lp ℂ ∞ (volume : Measure (ℝ^n))) (M : ℝ^n → ℂ)
    (hm : ⇑m =ᵐ[volume] M) (heven : ∀ ξ, M (-ξ) = M ξ)
    (hreal : ∀ ξ, star (M ξ) = M ξ)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hu : SobolevSpace.Fractional.IsRealL2 u) :
    SobolevSpace.Fractional.IsRealL2
      (PDE.Analysis.Fourier.fourierMultiplierL2 m u) := by
  apply (SobolevSpace.Fractional.isRealL2_iff_isHermitian_fourier _).2
  rw [PDE.Analysis.Fourier.fourierMultiplierL2_apply, fourier_fourierInv_eq]
  unfold SobolevSpace.Fractional.IsHermitianL2
  rw [SobolevSpace.Fractional.refl_star_lpSMul m M hm heven hreal]
  have hu' := (SobolevSpace.Fractional.isRealL2_iff_isHermitian_fourier u).1 hu
  exact congrArg (fun v : Lp ℂ 2 (volume : Measure (ℝ^n)) ↦ m • v) hu'

theorem heatL2_isReal (t : ℝ≥0)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hu : SobolevSpace.Fractional.IsRealL2 u) :
    SobolevSpace.Fractional.IsRealL2 (heatL2 n t u) := by
  apply fourierMultiplierL2_isReal (heatSymbolLinf n t) (heatSymbol n t)
    (MemLp.coeFn_toLp _) _ _ u hu
  · intro ξ
    simp [heatSymbol, norm_neg]
  · intro ξ
    exact Complex.conj_ofReal _

/-- A concrete one-order gaining operator on Bessel spaces. -/
def heatGainBessel (n : ℕ) (s t : ℝ) (ht : 0 < t) :
    H^{s}(ℝ^n) →L[ℂ] H^{s + 1}(ℝ^n) :=
  ((toLpₗᵢ (ℝ^n) ℂ (s + 1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((PDE.Analysis.Fourier.fourierMultiplierL2 (gainSymbolLinf n t ht)).comp
      (toLpₗᵢ (ℝ^n) ℂ s 2).toContinuousLinearEquiv.toContinuousLinearMap)

theorem norm_heatGainBessel_le (s : ℝ) {t : ℝ} (ht : 0 < t)
    (u : H^{s}(ℝ^n)) :
    ‖heatGainBessel n s t ht u‖ ≤ gainBound t * ‖u‖ := by
  change ‖(toLpₗᵢ (ℝ^n) ℂ (s + 1) 2).symm
    (PDE.Analysis.Fourier.fourierMultiplierL2 (gainSymbolLinf n t ht)
      ((toLpₗᵢ (ℝ^n) ℂ s 2) u))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (PDE.Analysis.Fourier.norm_fourierMultiplierL2_apply_le _ _).trans
    (by simpa using (mul_le_mul_of_nonneg_right
      (norm_gainSymbolLinf_le (n := n) ht) (norm_nonneg u)))

/-- The Bessel L² representative is the concrete reduced Fourier multiplier. -/
theorem toLp_heatGainBessel (s : ℝ) {t : ℝ} (ht : 0 < t) (u : H^{s}(ℝ^n)) :
    toLp (heatGainBessel n s t ht u) =
      PDE.Analysis.Fourier.fourierMultiplierL2 (gainSymbolLinf n t ht) (toLp u) := by
  simp only [heatGainBessel, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  simpa only [toLpₗᵢ_apply] using (toLpₗᵢ (ℝ^n) ℂ (s + 1) 2).apply_symm_apply
    (PDE.Analysis.Fourier.fourierMultiplierL2 (gainSymbolLinf n t ht) (toLp u))

theorem heatGainBessel_mem_real (s : ℝ) {t : ℝ} (ht : 0 < t)
    (u : H^{s}(ℝ^n)) (hu : u ∈ SobolevSpace.Fractional.hsRealSubmodule n s) :
    heatGainBessel n s t ht u ∈ SobolevSpace.Fractional.hsRealSubmodule n (s + 1) := by
  rw [SobolevSpace.Fractional.mem_HsRealSubmodule_iff] at hu ⊢
  rw [toLp_heatGainBessel]
  apply fourierMultiplierL2_isReal (gainSymbolLinf n t ht) (gainSymbol n t)
    (MemLp.coeFn_toLp _) _ _ (toLp u) hu
  · intro ξ
    simp [gainSymbol, norm_neg]
  · intro ξ
    exact Complex.conj_ofReal _

/-- The Bessel representative of the gaining operator has the reduced symbol. -/
theorem fourier_toLp_heatGainBessel (s : ℝ) {t : ℝ} (ht : 0 < t)
    (u : H^{s}(ℝ^n)) :
    𝓕 (toLp (heatGainBessel n s t ht u)) =
      (gainSymbolLinf n t ht • 𝓕 (toLp u) : Lp ℂ 2 (volume : Measure (ℝ^n))) := by
  rw [toLp_heatGainBessel, PDE.Analysis.Fourier.fourierMultiplierL2_apply,
    fourier_fourierInv_eq]

/-- The gaining operator represents the actual physical heat evolution. -/
theorem toL2Fun_heatGainBessel {s : ℝ} (hs : 0 ≤ s) (t : ℝ≥0)
    (ht : 0 < (t : ℝ)) (u : H^{s}(ℝ^n)) :
    SobolevSpace.Fractional.toL2Fun (show 0 ≤ s + 1 by linarith)
        (heatGainBessel n s (t : ℝ) ht u) =
      heatL2 n t (SobolevSpace.Fractional.toL2Fun hs u) := by
  apply (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).injective
  change 𝓕 (SobolevSpace.Fractional.toL2Fun _ _) = 𝓕 (heatL2 n t _)
  rw [heatL2, PDE.Analysis.Fourier.fourierMultiplierL2_apply, fourier_fourierInv_eq]
  apply Lp.ext
  have hrep := Lp.ext_iff.mp (fourier_toLp_heatGainBessel s ht u)
  have hgainAE : ⇑(gainSymbolLinf n (t : ℝ) ht) =ᵐ[volume] gainSymbol n (t : ℝ) :=
    (memLp_top_gainSymbol (n := n) ht).coeFn_toLp
  have hheatAE : ⇑(heatSymbolLinf n t) =ᵐ[volume] heatSymbol n t :=
    (memLp_top_heatSymbol (n := n) t).coeFn_toLp
  filter_upwards [SobolevSpace.Fractional.coeFn_fourier_toLp
      (show 0 ≤ s + 1 by linarith) (heatGainBessel n s (t : ℝ) ht u),
    SobolevSpace.Fractional.coeFn_fourier_toLp hs u, hrep,
    Lp.coeFn_lpSMul (r := 2) (gainSymbolLinf n (t : ℝ) ht) (𝓕 (toLp u)),
    hgainAE,
    Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n t)
      (𝓕 (SobolevSpace.Fractional.toL2Fun hs u)),
    hheatAE]
    with ξ hv hu hrep hgain hgainrep hheat hheatrep
  apply mul_left_cancel₀ (SobolevSpace.Fractional.besselSymbol_ne_zero (s + 1) ξ)
  rw [hheat, Pi.smul_apply', smul_eq_mul, hheatrep]
  calc
    _ = (𝓕 (toLp (heatGainBessel n s (t : ℝ) ht u)) :
        Lp ℂ 2 (volume : Measure (ℝ^n))) ξ := hv.symm
    _ = gainSymbol n (t : ℝ) ξ *
        (SobolevSpace.Fractional.besselSymbol n s ξ *
          (𝓕 (SobolevSpace.Fractional.toL2Fun hs u) :
            Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) := by
      rw [hrep, hgain, Pi.smul_apply', smul_eq_mul, hgainrep, hu]
    _ = _ := by rw [← mul_assoc, ← gainSymbol_factorization s t ξ]; ring

end HeatEquation.WholeSpace
