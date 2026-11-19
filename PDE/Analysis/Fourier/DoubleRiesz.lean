/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.L2Multiplier
public import PDE.DistributionTheory.TemperedDistribution.Sobolev.Fourier
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Conjugation
public import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalHigherOrder
public import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
public import PDE.FDeriv.Operators

/-!
# Double Riesz transforms on L²

The double Riesz transform `RᵢRⱼ` on `L²(ℝⁿ)` is the Fourier multiplier with the bounded
symbol `-ξᵢ ξⱼ / ‖ξ‖²`. It is a contraction, it maps real functions to real functions, and it
is the operator that recovers the pressure `Σ RᵢRⱼ (uᵢuⱼ)` of incompressible flow: tested with
the Laplacian of `g`, the transform `RᵢRⱼ f` pairs as `-f` against the second derivative
`∂ᵢ∂ⱼ g`, so `Δ (RᵢRⱼ f) = -∂ᵢ∂ⱼ f` in the weak sense. The symbol is bounded by one, so the
transform preserves square integrability of every Fourier weight, in particular every
Bessel-potential space.
-/

@[expose] public section

noncomputable section

open FourierTransform MeasureTheory Set Complex
open scoped ENNReal ComplexConjugate

namespace PDE.Analysis.Fourier

variable {n : ℕ}

/-- The symbol `-ξᵢ ξⱼ / ‖ξ‖²` of the double Riesz transform `RᵢRⱼ`; it vanishes at the
origin. -/
def doubleRieszSymbol (i j : Fin n) (ξ : ℝ^n) : ℂ :=
  ((-(ξ i * ξ j) / ‖ξ‖ ^ 2 : ℝ) : ℂ)

private theorem abs_mul_apply_le_norm_sq (ξ : ℝ^n) (i j : Fin n) : |ξ i * ξ j| ≤ ‖ξ‖ ^ 2 := by
  rw [abs_mul, sq]
  exact mul_le_mul (PiLp.norm_apply_le ξ i) (PiLp.norm_apply_le ξ j) (abs_nonneg _)
    (norm_nonneg _)

/-- The double Riesz symbol is bounded by one. -/
theorem norm_doubleRieszSymbol_le (i j : Fin n) (ξ : ℝ^n) : ‖doubleRieszSymbol i j ξ‖ ≤ 1 := by
  rw [doubleRieszSymbol, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg]
  rcases eq_or_lt_of_le (sq_nonneg ‖ξ‖) with h | h
  · rw [← h, abs_zero, div_zero]
    exact zero_le_one
  · rw [abs_of_pos h, div_le_one h]
    exact abs_mul_apply_le_norm_sq ξ i j

/-- Multiplying the symbol by `‖ξ‖²` gives the polynomial `-ξᵢ ξⱼ`, also at the origin. -/
theorem doubleRieszSymbol_mul_norm_sq (i j : Fin n) (ξ : ℝ^n) :
    doubleRieszSymbol i j ξ * ((‖ξ‖ ^ 2 : ℝ) : ℂ) = ((-(ξ i * ξ j) : ℝ) : ℂ) := by
  rw [doubleRieszSymbol, ← Complex.ofReal_mul]
  congr 1
  rcases eq_or_lt_of_le (sq_nonneg ‖ξ‖) with h | h
  · have hξ : ξ = 0 := by
      have : ‖ξ‖ = 0 := by nlinarith [norm_nonneg ξ]
      exact norm_eq_zero.mp this
    simp [hξ]
  · exact div_mul_cancel₀ _ h.ne'

/-- The double Riesz symbol is measurable. -/
theorem measurable_doubleRieszSymbol (i j : Fin n) :
    Measurable (doubleRieszSymbol (n := n) i j) := by
  unfold doubleRieszSymbol
  fun_prop

/-- The double Riesz symbol is even. -/
theorem doubleRieszSymbol_neg (i j : Fin n) (ξ : ℝ^n) :
    doubleRieszSymbol i j (-ξ) = doubleRieszSymbol i j ξ := by
  simp [doubleRieszSymbol]

/-- The double Riesz symbol is real. -/
theorem conj_doubleRieszSymbol (i j : Fin n) (ξ : ℝ^n) :
    conj (doubleRieszSymbol i j ξ) = doubleRieszSymbol i j ξ :=
  Complex.conj_ofReal _

/-- The double Riesz symbol is essentially bounded. -/
theorem memLp_top_doubleRieszSymbol (i j : Fin n) :
    MemLp (doubleRieszSymbol (n := n) i j) ∞ volume :=
  memLp_top_of_bound (measurable_doubleRieszSymbol i j).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (norm_doubleRieszSymbol_le i j))

/-- The double Riesz symbol as an `L∞` class. -/
def doubleRieszSymbolLinf (i j : Fin n) : Lp ℂ ∞ (volume : Measure (ℝ^n)) :=
  (memLp_top_doubleRieszSymbol i j).toLp _

/-- The `L∞` class of the double Riesz symbol has norm at most one. -/
theorem norm_doubleRieszSymbolLinf_le (i j : Fin n) :
    ‖doubleRieszSymbolLinf (n := n) i j‖ ≤ 1 := by
  rw [doubleRieszSymbolLinf, Lp.norm_toLp, eLpNorm_exponent_top]
  · exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (eLpNormEssSup_le_of_ae_bound (μ := (volume : Measure (ℝ^n)))
        (Filter.Eventually.of_forall (norm_doubleRieszSymbol_le (n := n) i j)))
  · exact (measurable_doubleRieszSymbol i j).aestronglyMeasurable

/-- The double Riesz transform `RᵢRⱼ` on complex `L²(ℝⁿ)`. -/
def doubleRiesz (i j : Fin n) :
    Lp ℂ 2 (volume : Measure (ℝ^n)) →L[ℂ] Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  fourierMultiplierL2 (doubleRieszSymbolLinf i j)

/-- The double Riesz transform is a contraction of `L²`. -/
theorem norm_doubleRiesz_apply_le (i j : Fin n) (f : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    ‖doubleRiesz i j f‖ ≤ ‖f‖ :=
  (norm_fourierMultiplierL2_apply_le _ f).trans
    (mul_le_of_le_one_left (norm_nonneg f) (norm_doubleRieszSymbolLinf_le i j))

/-- The Fourier transform of `RᵢRⱼ f` is the symbol times the Fourier transform of `f`. -/
theorem fourier_doubleRiesz_ae (i j : Fin n) (f : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    ((𝓕 (doubleRiesz i j f) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) =ᵐ[volume]
      fun ξ ↦ doubleRieszSymbol i j ξ * (𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ := by
  rw [doubleRiesz, fourierMultiplierL2_apply, fourier_fourierInv_eq]
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (doubleRieszSymbolLinf (n := n) i j) (𝓕 f),
    (memLp_top_doubleRieszSymbol (n := n) i j).coeFn_toLp] with ξ h1 h2
  rw [h1, Pi.smul_apply', smul_eq_mul, doubleRieszSymbolLinf, h2]

/-- The Fourier multiplier of a derivative word of length two. -/
private theorem prod_pair_apply (c : ℂ) (ξ : ℝ^n) (i j : Fin n) :
    (∏ m : Fin [i, j].length, c * (ξ ([i, j].get m) : ℂ)) = (c * ξ i) * (c * ξ j) := by
  change ∏ m : Fin 2, c * (ξ ([i, j].get m) : ℂ) = _
  rw [Fin.prod_univ_two]
  rfl

/-- Weak second derivatives in the directions `k, k` add up, on the Fourier side, to the
multiplier `-4π²‖ξ‖²` of the Laplacian. -/
theorem fourier_sum_ae_of_hasComplexWeakDerivativeOn (g : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (d : Fin n → Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hd : ∀ k, SobolevSpace.HasComplexWeakDerivativeOn univ [k, k] g (d k)) :
    ((𝓕 (∑ k, d k) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) =ᵐ[volume]
      fun ξ ↦ -((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
        (𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ := by
  have hF := fun k ↦ (SobolevSpace.hasComplexWeakDerivativeOn_iff_fourier [k, k] g (d k)).1 (hd k)
  have hsum : (𝓕 (∑ k, d k) : Lp ℂ 2 (volume : Measure (ℝ^n))) = ∑ k, 𝓕 (d k) :=
    map_sum (Lp.fourierTransformₗᵢ (ℝ^n) ℂ) d Finset.univ
  rw [hsum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun k ↦ (𝓕 (d k) :
      Lp ℂ 2 (volume : Measure (ℝ^n)))), ae_all_iff.2 hF] with ξ hs hk
  rw [hs, Finset.sum_apply]
  simp only [prod_pair_apply] at hk
  simp only [← hk]
  rw [← Finset.sum_mul]
  congr 1
  have hnorm : ‖ξ‖ ^ 2 = ∑ k : Fin n, ξ k ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  rw [hnorm]
  push_cast
  rw [Finset.mul_sum, neg_eq_neg_one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  linear_combination (4 * (Real.pi : ℂ) ^ 2 * (ξ k : ℂ) ^ 2) * Complex.I_sq

/-- Weak form of `Δ (RᵢRⱼ f) = -∂ᵢ∂ⱼ f`. If the Fourier transform of `D` is
`-4π²‖ξ‖²` times that of `g`, and `e` is the weak derivative `∂ᵢ∂ⱼ g`, then
`⟪RᵢRⱼ f, D⟫ = -⟪f, e⟫`. -/
theorem inner_doubleRiesz_eq_neg (i j : Fin n) (f g D e : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hD : ((𝓕 D : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) =ᵐ[volume]
      fun ξ ↦ -((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
        (𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ)
    (he : SobolevSpace.HasComplexWeakDerivativeOn univ [i, j] g e) :
    inner ℂ (doubleRiesz i j f) D = -inner ℂ f e := by
  have heF := (SobolevSpace.hasComplexWeakDerivativeOn_iff_fourier [i, j] g e).1 he
  rw [← Lp.inner_fourier_eq, ← Lp.inner_fourier_eq f e, L2.inner_def, L2.inner_def,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [fourier_doubleRiesz_ae i j f, hD, heF] with ξ h1 h2 h3
  simp only [prod_pair_apply] at h3
  rw [h1, h2, ← h3]
  simp only [RCLike.inner_apply, map_mul, conj_doubleRieszSymbol]
  have hsym := doubleRieszSymbol_mul_norm_sq i j ξ
  push_cast at hsym ⊢
  linear_combination (-(4 : ℂ) * (Real.pi : ℂ) ^ 2 *
    conj ((𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) *
    (𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) * hsym +
    (4 * (Real.pi : ℂ) ^ 2 * (ξ i : ℂ) * (ξ j : ℂ) *
    conj ((𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) *
    (𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) * Complex.I_sq

/-- The double Riesz transform maps real `L²` functions to real `L²` functions, because its
symbol is real and even. -/
theorem isRealL2_doubleRiesz (i j : Fin n) {f : Lp ℂ 2 (volume : Measure (ℝ^n))}
    (hf : SobolevSpace.Fractional.IsRealL2 f) :
    SobolevSpace.Fractional.IsRealL2 (doubleRiesz i j f) := by
  rw [SobolevSpace.Fractional.isRealL2_iff_isHermitian_fourier, doubleRiesz,
    fourierMultiplierL2_apply, fourier_fourierInv_eq]
  rw [SobolevSpace.Fractional.isRealL2_iff_isHermitian_fourier] at hf
  unfold SobolevSpace.Fractional.IsHermitianL2 at hf ⊢
  rw [SobolevSpace.Fractional.refl_star_lpSMul (doubleRieszSymbolLinf i j) (doubleRieszSymbol i j)
    (memLp_top_doubleRieszSymbol i j).coeFn_toLp (doubleRieszSymbol_neg i j)
    (conj_doubleRieszSymbol i j), hf]

/-- The double Riesz transform preserves square integrability of any Fourier weight, in
particular every Bessel-potential space. -/
theorem memLp_weight_mul_fourier_doubleRiesz (i j : Fin n) {w : ℝ^n → ℂ} (hw : Measurable w)
    {f : Lp ℂ 2 (volume : Measure (ℝ^n))}
    (hf : MemLp (fun ξ ↦ w ξ * (𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) 2 volume) :
    MemLp (fun ξ ↦ w ξ * (𝓕 (doubleRiesz i j f) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ)
      2 volume := by
  refine hf.of_le (hw.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)) ?_
  filter_upwards [fourier_doubleRiesz_ae i j f] with ξ hξ
  rw [hξ, norm_mul, norm_mul, norm_mul, mul_left_comm]
  exact mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (norm_doubleRieszSymbol_le i j ξ)

/-! ## Real test functions -/

/-- The complex `L²` class of a real continuous compactly supported function. -/
def realTestL2 {χ : ℝ^n → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  ((Complex.continuous_ofReal.comp hχ).memLp_of_hasCompactSupport
    (hc.comp_left Complex.ofReal_zero)).toLp (fun x ↦ (χ x : ℂ))

/-- The class `realTestL2` is represented by the complexified function. -/
theorem coeFn_realTestL2 {χ : ℝ^n → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    (realTestL2 hχ hc : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (χ x : ℂ) :=
  MemLp.coeFn_toLp _

/-- Classical derivatives of a smooth compactly supported real function are complex weak
derivatives of its complex `L²` class. -/
theorem hasComplexWeakDerivativeOn_realTestL2 {χ : ℝ^n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (α : List (Fin n)) :
    SobolevSpace.HasComplexWeakDerivativeOn univ α (realTestL2 hχ.continuous hc)
      (realTestL2 (contDiff_top_iteratedPartialDeriv hχ α).continuous
        (hc.iteratedPartialDeriv α)) := by
  have hfun : SobolevSpace.HasComplexWeakDerivativeOn univ α (fun x ↦ (χ x : ℂ))
      (fun x ↦ ((iteratedPartialDeriv α χ x : ℝ) : ℂ)) := by
    refine ⟨?_, ?_⟩
    · simpa only [Complex.ofReal_re] using
        SobolevSpace.hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiffOn (k := α.length)
          isOpen_univ (hχ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)).contDiffOn
          α le_rfl
    · simpa only [Complex.ofReal_im] using SobolevSpace.hasWeakDerivativeOn_zero univ α
  refine hfun.congr_ae ?_ ?_
  · simpa [SobolevSpace.domainMeasure] using (coeFn_realTestL2 hχ.continuous hc).symm
  · simpa [SobolevSpace.domainMeasure] using (coeFn_realTestL2 _ _).symm

/-- The real part of an `L²` pairing with the class of a real function. -/
private theorem re_inner_eq_integral (A R : Lp ℂ 2 (volume : Measure (ℝ^n))) {r : ℝ^n → ℝ}
    (hR : (R : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (r x : ℂ)) :
    (inner ℂ A R).re = ∫ x, (A x).re * r x := by
  have hre := integral_re (L2.integrable_inner (𝕜 := ℂ) A R)
  simp only [RCLike.re_to_complex] at hre
  rw [L2.inner_def, ← hre]
  apply integral_congr_ae
  filter_upwards [hR] with x hx
  simp only [RCLike.inner_apply, hx, Complex.mul_re, Complex.conj_re,
    Complex.ofReal_re, Complex.conj_im, Complex.ofReal_im]
  ring

/-- Weak form of `Δ (RᵢRⱼ f) = -∂ᵢ∂ⱼ f` against a real test function: for every smooth
compactly supported `χ`, `∫ Re (RᵢRⱼ F) Δχ = -∫ Re F ∂ᵢ∂ⱼχ`. -/
theorem integral_re_doubleRiesz_mul_laplacian (i j : Fin n)
    (F : Lp ℂ 2 (volume : Measure (ℝ^n))) {χ : ℝ^n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) :
    ∫ x, (doubleRiesz i j F x).re * PDE.laplacian χ x =
      -∫ x, (F x).re * iteratedPartialDeriv [i, j] χ x := by
  set G := realTestL2 hχ.continuous hc
  set d : Fin n → Lp ℂ 2 (volume : Measure (ℝ^n)) := fun k ↦
    realTestL2 (contDiff_top_iteratedPartialDeriv hχ [k, k]).continuous
      (hc.iteratedPartialDeriv [k, k])
  set e := realTestL2 (contDiff_top_iteratedPartialDeriv hχ [i, j]).continuous
      (hc.iteratedPartialDeriv [i, j])
  have hD := fourier_sum_ae_of_hasComplexWeakDerivativeOn G d
    (fun k ↦ hasComplexWeakDerivativeOn_realTestL2 hχ hc [k, k])
  have key := inner_doubleRiesz_eq_neg i j F G (∑ k, d k) e hD
    (hasComplexWeakDerivativeOn_realTestL2 hχ hc [i, j])
  have hsum : ((∑ k, d k : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) =ᵐ[volume]
      fun x ↦ ((PDE.laplacian χ x : ℝ) : ℂ) := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ d,
      ae_all_iff.2 fun k ↦ coeFn_realTestL2 (contDiff_top_iteratedPartialDeriv hχ [k, k]).continuous
        (hc.iteratedPartialDeriv [k, k])] with x hx hk
    rw [hx, Finset.sum_apply, PDE.laplacian, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun k _ ↦ hk k
  rw [← re_inner_eq_integral _ _ hsum, key, Complex.neg_re,
    re_inner_eq_integral _ _ (coeFn_realTestL2 _ _)]

end PDE.Analysis.Fourier
