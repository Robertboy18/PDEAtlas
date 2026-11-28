/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.DistributionTheory.TemperedDistribution.Sobolev.Fourier
public import PDE.Analysis.Fourier.Agmon
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Energy

/-!
# Derivatives in Sobolev spaces of real order

A weak derivative `∂^α` of order `k = |α|` maps `H^{σ+k}(ℝⁿ)` to `H^σ(ℝⁿ)` for every real `σ`: if
`u ∈ L²(ℝⁿ)` has the weak derivative `v = ∂^α u` in `L²`, then `E_σ(v) ≤ (2π)^{2k} E_{σ+k}(u)`.
Conversely, a function with `E_k(u) < ∞` has all its weak derivatives of order `k` in `L²`, and
`u` is in `H^{σ+1}` exactly when `u` and its gradient are in `H^σ`. A term such as `u · ∇u` loses
one derivative, and the count of orders in a bootstrap rests on these facts. The statements are
about `L²` functions and their energies; `SobolevSpace.Fractional.derivCLM` is the bounded
operator they give, and `lineDerivCLM` is the derivative on Bessel potential spaces of
distributions. Negative orders `σ + |α| < 0`, where the functions are distributions and not in
`L²`, are not covered.

## Main results

* `HasComplexWeakDerivativeOn.unique_L2`, `.add_L2`, `.smul_L2`: on the whole space and for `L²`
  functions, the complex weak derivative `∂^α` is unique and linear.
* `besselEnergy_le_of_hasComplexWeakDerivativeOn`: `E_σ(∂^α u) ≤ (2π)^{2|α|} E_{σ+|α|}(u)` for every
  real `σ`.
* `exists_hasComplexWeakDerivativeOn_of_besselEnergy_lt_top`: if `E_{|α|}(u) < ∞`, the weak
  derivative `∂^α u` exists in `L²`.
* `besselEnergy_add_one_eq`: `E_{σ+1}(u) = E_σ(u) + (2π)^{-2} E_σ(∇u)` for every real `σ`.

## How it works

On the Fourier side a weak derivative `∂^α` is the multiplication by `∏ⱼ 2πi ξ_{αⱼ}`
(`SobolevSpace.hasComplexWeakDerivativeOn_iff_fourier`). Its modulus is at most
`(2π |ξ|)^k ≤ (2π)^k (1 + |ξ|²)^{k/2}` for a word of length `k`, which gives the bound of the
energy, and when `E_k(u)` is finite the multiplied transform is square integrable, which gives
the derivative. For `k = 1` the sum over the coordinates is an identity,
`(1 + |ξ|²)^{σ+1} = (1 + |ξ|²)^σ (1 + ∑ᵢ ξᵢ²)`. Uniqueness and linearity come from the injectivity
and linearity of the Fourier transform on `L²`. On other open sets, and for locally integrable
functions, they hold as well, but they are not proved here for complex derivatives; the real case
is `SobolevSpace.HasWeakDerivativeOn.unique_ae`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.5, Theorem 8, pp. 297-298, the characterization of
  `H^k(ℝ^n)` by the Fourier transform, with `(D^α u)^ = (iy)^α û`, (21), in step 1 of the proof,
  and step 2 of the proof, p. 298: if `(1 + |y|^k)û ∈ L²`, then `((iy)^α û)^∨` is the weak
  derivative `D^α u` for `|α| ≤ k`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal

namespace SobolevSpace.Fractional

variable {n : ℕ}

/-! ## The weak derivative is a linear partial map on `L²` -/

/-- **A function in `L²(ℝⁿ)` has at most one weak derivative `∂^α` in `L²`.** -/
theorem _root_.SobolevSpace.HasComplexWeakDerivativeOn.unique_L2 {α : List (Fin n)}
    {u v v' : Lp ℂ 2 (volume : Measure (ℝ^n))} (h : HasComplexWeakDerivativeOn univ α u v)
    (h' : HasComplexWeakDerivativeOn univ α u v') : v = v' :=
  (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).injective (Lp.ext
    (((hasComplexWeakDerivativeOn_iff_fourier α u v).1 h).symm.trans
      ((hasComplexWeakDerivativeOn_iff_fourier α u v').1 h')))

/-- **The weak derivative of a sum** of two functions in `L²(ℝⁿ)` is the sum of the weak
derivatives. -/
theorem _root_.SobolevSpace.HasComplexWeakDerivativeOn.add_L2 {α : List (Fin n)}
    {u u' v v' : Lp ℂ 2 (volume : Measure (ℝ^n))} (h : HasComplexWeakDerivativeOn univ α u v)
    (h' : HasComplexWeakDerivativeOn univ α u' v') :
    HasComplexWeakDerivativeOn univ α (u + u' : Lp ℂ 2 (volume : Measure (ℝ^n)))
      (v + v' : Lp ℂ 2 (volume : Measure (ℝ^n))) := by
  rw [hasComplexWeakDerivativeOn_iff_fourier] at h h' ⊢
  have e1 : (𝓕 (u + u') : Lp ℂ 2 (volume : Measure (ℝ^n))) = 𝓕 u + 𝓕 u' :=
    map_add (Lp.fourierTransformₗᵢ (ℝ^n) ℂ) u u'
  have e2 : (𝓕 (v + v') : Lp ℂ 2 (volume : Measure (ℝ^n))) = 𝓕 v + 𝓕 v' :=
    map_add (Lp.fourierTransformₗᵢ (ℝ^n) ℂ) v v'
  rw [e1, e2]
  filter_upwards [h, h', Lp.coeFn_add (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) (𝓕 u'),
    Lp.coeFn_add (𝓕 v : Lp ℂ 2 (volume : Measure (ℝ^n))) (𝓕 v')] with ξ h1 h2 h3 h4
  rw [h3, h4, Pi.add_apply, Pi.add_apply, mul_add, h1, h2]

/-- **The weak derivative of a multiple** of a function in `L²(ℝⁿ)` is the multiple of the weak
derivative. -/
theorem _root_.SobolevSpace.HasComplexWeakDerivativeOn.smul_L2 {α : List (Fin n)}
    {u v : Lp ℂ 2 (volume : Measure (ℝ^n))} (h : HasComplexWeakDerivativeOn univ α u v) (c : ℂ) :
    HasComplexWeakDerivativeOn univ α (c • u : Lp ℂ 2 (volume : Measure (ℝ^n)))
      (c • v : Lp ℂ 2 (volume : Measure (ℝ^n))) := by
  rw [hasComplexWeakDerivativeOn_iff_fourier] at h ⊢
  have e1 : (𝓕 (c • u) : Lp ℂ 2 (volume : Measure (ℝ^n))) = c • 𝓕 u :=
    map_smul (Lp.fourierTransformₗᵢ (ℝ^n) ℂ) c u
  have e2 : (𝓕 (c • v) : Lp ℂ 2 (volume : Measure (ℝ^n))) = c • 𝓕 v :=
    map_smul (Lp.fourierTransformₗᵢ (ℝ^n) ℂ) c v
  rw [e1, e2]
  filter_upwards [h, Lp.coeFn_smul c (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))),
    Lp.coeFn_smul c (𝓕 v : Lp ℂ 2 (volume : Measure (ℝ^n)))] with ξ h1 h3 h4
  rw [h3, h4, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, h1]

/-! ## The symbol of a derivative -/

/-- The symbol `∏ⱼ 2πi ξ_{αⱼ}` of the derivative `∂^α` is continuous. -/
theorem continuous_derivSymbol (α : List (Fin n)) :
    Continuous fun ξ : ℝ^n ↦ ∏ j : Fin α.length,
      (2 * Real.pi * Complex.I) * (ξ (α.get j) : ℂ) :=
  continuous_finsetProd _ fun j _ ↦ continuous_const.mul
    (Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ (α.get j)))

/-- **The symbol of a derivative of order `k` is bounded by the weight of order `k`**:
`|∏ⱼ 2πi ξ_{αⱼ}|² ≤ (2π)^{2k} (1 + |ξ|²)^k` for a word `α` of length `k`. -/
theorem enorm_derivSymbol_sq_le (α : List (Fin n)) (ξ : ℝ^n) :
    ‖∏ j : Fin α.length, (2 * Real.pi * Complex.I) * (ξ (α.get j) : ℂ)‖ₑ ^ 2 ≤
      ENNReal.ofReal ((2 * Real.pi) ^ (2 * α.length)) *
        (besselWeight n (α.length : ℝ) ξ : ℝ≥0∞) := by
  have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h2π : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      Complex.norm_real, Real.norm_of_nonneg hπ]
  have hnorm : ‖∏ j : Fin α.length, (2 * Real.pi * Complex.I) * (ξ (α.get j) : ℂ)‖ ≤
      (2 * Real.pi * ‖ξ‖) ^ α.length := by
    rw [norm_prod]
    refine (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun j _ ↦ ?_).trans_eq
      (by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin])
    rw [norm_mul, h2π, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le ξ (α.get j)) hπ
  have hsq : ‖∏ j : Fin α.length, (2 * Real.pi * Complex.I) * (ξ (α.get j) : ℂ)‖ ^ 2 ≤
      (2 * Real.pi) ^ (2 * α.length) * (1 + ‖ξ‖ ^ 2) ^ (α.length : ℝ) := by
    refine (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans ?_
    rw [Real.rpow_natCast, ← pow_mul, mul_comm α.length 2, mul_pow, pow_mul ‖ξ‖]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sq_nonneg _) (by linarith) _) (by positivity)
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), coe_besselWeight,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hsq

/-- **A derivative of order `k` maps `H^{σ+k}` to `H^σ`.** Let `u ∈ L²(ℝⁿ)` have the weak
derivative `v = ∂^α u` in `L²`, for a word `α` of length `k`. Then, for every real `σ`,
`E_σ(v) ≤ (2π)^{2k} E_{σ+k}(u)`. -/
theorem besselEnergy_le_of_hasComplexWeakDerivativeOn (σ : ℝ) (α : List (Fin n))
    (u v : Lp ℂ 2 (volume : Measure (ℝ^n))) (h : HasComplexWeakDerivativeOn univ α u v) :
    besselEnergy σ (fun _ : Unit ↦ v) ≤ ENNReal.ofReal ((2 * Real.pi) ^ (2 * α.length)) *
      besselEnergy (σ + α.length) (fun _ : Unit ↦ u) := by
  simp only [besselEnergy_unit_eq_lintegral]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [(hasComplexWeakDerivativeOn_iff_fourier α u v).1 h] with ξ hξ
  rw [← hξ, eNorm_mul, mul_pow, besselWeight_add, ENNReal.coe_mul]
  calc (besselWeight n σ ξ : ℝ≥0∞) * (‖∏ j : Fin α.length,
        (2 * Real.pi * Complex.I) * (ξ (α.get j) : ℂ)‖ₑ ^ 2 *
          ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2)
      ≤ (besselWeight n σ ξ : ℝ≥0∞) * (ENNReal.ofReal ((2 * Real.pi) ^ (2 * α.length)) *
          (besselWeight n (α.length : ℝ) ξ : ℝ≥0∞) *
            ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2) :=
        mul_le_mul' le_rfl (mul_le_mul' (enorm_derivSymbol_sq_le α ξ) le_rfl)
    _ = _ := by ring

/-- **A function of finite energy of order `k` has its weak derivatives of order `k` in `L²`.**
For every word `α` of length `k` and every `u ∈ L²(ℝⁿ)` with `E_k(u) < ∞` there is `v ∈ L²`
with `v = ∂^α u` weakly. -/
theorem exists_hasComplexWeakDerivativeOn_of_besselEnergy_lt_top (α : List (Fin n))
    (u : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (h : besselEnergy (α.length : ℝ) (fun _ : Unit ↦ u) < ⊤) :
    ∃ v : Lp ℂ 2 (volume : Measure (ℝ^n)), HasComplexWeakDerivativeOn univ α u v := by
  rw [exists_hasComplexWeakDerivativeOn_iff_memLp_fourier]
  have hm : AEStronglyMeasurable (fun ξ : ℝ^n ↦ (∏ j : Fin α.length,
      (2 * Real.pi * Complex.I) * (ξ (α.get j) : ℂ)) *
        (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) volume :=
    (continuous_derivSymbol α).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hm
  have h3 : eLpNorm (fun ξ : ℝ^n ↦ (∏ j : Fin α.length,
      (2 * Real.pi * Complex.I) * (ξ (α.get j) : ℂ)) *
        (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) 2 volume ^ 2 ≤
      ENNReal.ofReal ((2 * Real.pi) ^ (2 * α.length)) *
        besselEnergy (α.length : ℝ) (fun _ : Unit ↦ u) := by
    have h4 : eLpNorm (fun ξ : ℝ^n ↦ (∏ j : Fin α.length,
        (2 * Real.pi * Complex.I) * (ξ (α.get j) : ℂ)) *
          (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) 2 volume ^ 2 =
        ∫⁻ ξ, ‖(∏ j : Fin α.length, (2 * Real.pi * Complex.I) * (ξ (α.get j) : ℂ)) *
          (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 := by
      simpa [ENNReal.rpow_two] using h2
    rw [h4, besselEnergy_unit_eq_lintegral, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ξ ↦ ?_
    rw [eNorm_mul, mul_pow, ← mul_assoc]
    exact mul_le_mul' (enorm_derivSymbol_sq_le α ξ) le_rfl
  by_contra hcon
  rw [MemLp, not_lt, top_le_iff] at hcon
  rw [hcon] at h3
  exact absurd (h3.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)) (by simp)

/-- **The norm of `H^{σ+1}` is the norm of `H^σ` of the function and of its gradient.** Let
`u ∈ L²(ℝⁿ)` have the weak first derivatives `d i = ∂ᵢu` in `L²`. Then, for every real `σ`,
`E_{σ+1}(u) = E_σ(u) + (2π)^{-2} E_σ(d)`, where `E_σ(d) = ∑ᵢ E_σ(d i)`. In particular `u` is in
`H^{σ+1}` exactly when `u` and its gradient are in `H^σ`. -/
theorem besselEnergy_add_one_eq (σ : ℝ) (u : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (d : Fin n → Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hd : ∀ i, HasComplexWeakDerivativeOn univ [i] u (d i)) :
    besselEnergy (σ + 1) (fun _ : Unit ↦ u) = besselEnergy σ (fun _ : Unit ↦ u) +
      ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * besselEnergy σ d := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmw : Measurable fun ξ : ℝ^n ↦ (besselWeight n σ ξ : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (measurable_besselWeight σ)
  have hmu : Measurable fun ξ ↦ ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 :=
    (Lp.stronglyMeasurable _).eNorm.pow_const 2
  have hmwu : Measurable fun ξ ↦ (besselWeight n σ ξ : ℝ≥0∞) *
      ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 := hmw.mul hmu
  -- the transform of each derivative
  have hF (i : Fin n) : ∀ᵐ ξ : ℝ^n, ‖(𝓕 (d i) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 =
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * (ENNReal.ofReal (ξ i ^ 2) *
        ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2) := by
    filter_upwards [(hasComplexWeakDerivativeOn_iff_fourier [i] u (d i)).1 (hd i)] with ξ hξ
    rw [← hξ, PDE.Analysis.Fourier.prod_single_apply, eNorm_mul, mul_pow, ← mul_assoc]
    congr 1
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs, ENNReal.ofReal_mul (sq_nonneg _)]
    congr 3
    rw [norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      Complex.norm_real, Real.norm_of_nonneg hπ.le]
  -- the weight of order one
  have hw1 (ξ : ℝ^n) : (besselWeight n 1 ξ : ℝ≥0∞) = 1 + ∑ i, ENNReal.ofReal (ξ i ^ 2) := by
    rw [coe_besselWeight, Real.rpow_one, ENNReal.ofReal_add zero_le_one (sq_nonneg _),
      ENNReal.ofReal_one, EuclideanSpace.real_norm_sq_eq,
      ENNReal.ofReal_sum_of_nonneg fun i _ ↦ sq_nonneg _]
  have hc : ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ENNReal.ofReal ((2 * Real.pi) ^ 2) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity),
      ENNReal.ofReal_one]
  rw [besselEnergy_unit_eq_lintegral, besselEnergy_unit_eq_lintegral, besselEnergy,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left hmwu]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_all_iff.2 hF] with ξ hξ
  simp only [fourierDensity, hξ]
  rw [besselWeight_add, ENNReal.coe_mul, hw1, ← Finset.mul_sum, ← Finset.sum_mul]
  calc (besselWeight n σ ξ : ℝ≥0∞) * (1 + ∑ i, ENNReal.ofReal (ξ i ^ 2)) *
        ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2
      = (besselWeight n σ ξ : ℝ≥0∞) * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 +
          (ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ENNReal.ofReal ((2 * Real.pi) ^ 2)) *
            ((besselWeight n σ ξ : ℝ≥0∞) * ((∑ i, ENNReal.ofReal (ξ i ^ 2)) *
              ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2)) := by
        rw [hc]
        ring
    _ = _ := by ring

end SobolevSpace.Fractional
