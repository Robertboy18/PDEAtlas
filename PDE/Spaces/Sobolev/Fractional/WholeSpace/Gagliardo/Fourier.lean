/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.GagliardoFourier
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.FourierWeight

/-!
# Homogeneous and inhomogeneous fractional Fourier weights

The homogeneous multiplier `‖ξ‖^s` characterizes positive-order Bessel regularity once the
physical function is in `L²`. Its norm is exactly the Fourier seminorm used by the
Gagliardo identity. The inhomogeneous norm is bounded by the sum of the physical `L²`
norm and this homogeneous norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution BesselPotentialSpace
open scoped BesselPotentialSpace ENNReal FourierTransform SchwartzMap

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ}

/-- The homogeneous fractional Fourier multiplier applied to the physical `L²` transform. -/
def homogeneousWeightedFourier (s : ℝ) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    ℝ^n → ℂ :=
  fun ξ ↦ (‖ξ‖ ^ s : ℝ) • (𝓕 u) ξ

private theorem aestronglyMeasurable_homogeneousWeightedFourier
    (s : ℝ) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    AEStronglyMeasurable (homogeneousWeightedFourier s u) volume :=
  (by fun_prop : Measurable (fun ξ : ℝ^n ↦ ‖ξ‖ ^ s)).aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable _)

/-- The homogeneous Fourier seminorm is the square of the weighted `L²` seminorm. -/
theorem fourierSq_eq_eLpNorm_sq
    (s : ℝ) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    fourierSq n s (𝓕 u : Lp ℂ 2 volume) =
      eLpNorm (homogeneousWeightedFourier s u) 2 volume ^ 2 := by
  rw [show eLpNorm (homogeneousWeightedFourier s u) 2 volume ^ 2 =
      ∫⁻ ξ, ‖homogeneousWeightedFourier s u ξ‖ₑ ^ 2 by
    simpa [ENNReal.rpow_two] using
      (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num)
        (aestronglyMeasurable_homogeneousWeightedFourier s u))]
  refine lintegral_congr fun ξ ↦ ?_
  have hpow : (‖ξ‖ ^ s) ^ (2 : ℕ) = ‖ξ‖ ^ (2 * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg ξ), mul_comm]
    norm_num
  simp only [homogeneousWeightedFourier, enorm_smul,
    Real.enorm_eq_ofReal (Real.rpow_nonneg (norm_nonneg ξ) s), mul_pow]
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (norm_nonneg ξ) s), hpow]

/-- Finiteness of the homogeneous Fourier integral is precisely weighted `L²` membership. -/
theorem memLp_homogeneousWeightedFourier_iff
    (s : ℝ) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    MemLp (homogeneousWeightedFourier s u) 2 volume ↔
      fourierSq n s (𝓕 u : Lp ℂ 2 volume) < ⊤ := by
  rw [fourierSq_eq_eLpNorm_sq]
  exact ⟨fun h ↦ ENNReal.pow_lt_top h,
    fun h ↦ (ENNReal.pow_lt_top_iff.mp h).resolve_right (by norm_num)⟩

private theorem norm_homogeneousWeightedFourier (u : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (ξ : ℝ^n) :
    ‖homogeneousWeightedFourier s u ξ‖ = ‖ξ‖ ^ s * ‖(𝓕 u) ξ‖ := by
  rw [homogeneousWeightedFourier, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg ξ) s)]

private theorem norm_besselSymbol_mul (u : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (ξ : ℝ^n) :
    ‖besselSymbol n s ξ * (𝓕 u) ξ‖ =
      (1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖(𝓕 u) ξ‖ := by
  rw [norm_mul, besselSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

private theorem homogeneousWeight_le_besselWeight (hs : 0 ≤ s) (ξ : ℝ^n) :
    ‖ξ‖ ^ s ≤ (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by
  rw [show ‖ξ‖ ^ s = (‖ξ‖ ^ 2) ^ (s / 2) by
    rw [Real.rpow_div_two_eq_sqrt s (sq_nonneg _), Real.sqrt_sq (norm_nonneg ξ)]]
  exact Real.rpow_le_rpow (sq_nonneg _) (by linarith) (by positivity)

private theorem besselWeight_le_one_add_homogeneousWeight
    (hs : 0 ≤ s) (hs2 : s ≤ 2) (ξ : ℝ^n) :
    (1 + ‖ξ‖ ^ 2) ^ (s / 2) ≤ 1 + ‖ξ‖ ^ s := by
  rw [show ‖ξ‖ ^ s = (‖ξ‖ ^ 2) ^ (s / 2) by
    rw [Real.rpow_div_two_eq_sqrt s (sq_nonneg _), Real.sqrt_sq (norm_nonneg ξ)]]
  simpa only [Real.one_rpow] using Real.rpow_add_le_add_rpow
    zero_le_one (sq_nonneg ‖ξ‖) (by positivity : 0 ≤ s / 2) (by linarith : s / 2 ≤ 1)

/-- The physical `L²` condition supplies the low frequencies; the homogeneous weight
supplies the remaining Bessel regularity. -/
theorem memSobolev_iff_memLp_homogeneousWeightedFourier
    (hs : 0 ≤ s) (hs2 : s ≤ 2) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    MemSobolev s 2 (u : 𝓢'(ℝ^n, ℂ)) ↔
      MemLp (homogeneousWeightedFourier s u) 2 volume := by
  rw [memSobolev_iff_memLp_besselWeight]
  constructor
  · intro h
    apply h.mono (aestronglyMeasurable_homogeneousWeightedFourier s u)
    exact Filter.Eventually.of_forall fun ξ ↦ by
      rw [norm_homogeneousWeightedFourier, norm_besselSymbol_mul]
      exact mul_le_mul_of_nonneg_right (homogeneousWeight_le_besselWeight hs ξ)
        (norm_nonneg _)
  · intro h
    apply ((Lp.memLp (𝓕 u)).norm.add h.norm).mono
      ((by unfold besselSymbol; fun_prop : Measurable (besselSymbol n s)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable _))
    exact Filter.Eventually.of_forall fun ξ ↦ by
      change ‖besselSymbol n s ξ * (𝓕 u) ξ‖ ≤
        ‖‖(𝓕 u) ξ‖ + ‖homogeneousWeightedFourier s u ξ‖‖
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_besselSymbol_mul,
        norm_homogeneousWeightedFourier]
      nlinarith [mul_le_mul_of_nonneg_right
        (besselWeight_le_one_add_homogeneousWeight hs hs2 ξ) (norm_nonneg ((𝓕 u) ξ))]

/-- A nonnegative-order Bessel element has a square-integrable homogeneous transform. -/
theorem memLp_homogeneousWeightedFourier_toL2Fun (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) :
    MemLp (homogeneousWeightedFourier s (toL2Fun hs u)) 2 volume := by
  have h := (memSobolev_iff_memLp_besselWeight s (toL2Fun hs u)).mp
    (by rw [← toDistr_eq_toL2Fun]; exact u.memSobolev_toDistr)
  apply h.mono (aestronglyMeasurable_homogeneousWeightedFourier s _)
  exact Filter.Eventually.of_forall fun ξ ↦ by
    rw [norm_homogeneousWeightedFourier, norm_besselSymbol_mul]
    exact mul_le_mul_of_nonneg_right (homogeneousWeight_le_besselWeight hs ξ)
      (norm_nonneg _)

/-- The homogeneous fractional transform of a Bessel element, as an `L²` class. -/
def homogeneousFourierLp (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) :
    Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  (memLp_homogeneousWeightedFourier_toL2Fun hs u).toLp _

/-- The homogeneous `L²` class represents `‖ξ‖^s 𝓕u` almost everywhere. -/
theorem coeFn_homogeneousFourierLp (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) :
    (homogeneousFourierLp hs u : ℝ^n → ℂ) =ᵐ[volume]
      homogeneousWeightedFourier s (toL2Fun hs u) :=
  MemLp.coeFn_toLp _

/-- The homogeneous Fourier integral of a Bessel element is finite and equals a squared norm. -/
theorem fourierSq_eq_norm_homogeneousFourierLp_sq (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) :
    fourierSq n s (𝓕 (toL2Fun hs u) : Lp ℂ 2 volume) =
      ENNReal.ofReal (‖homogeneousFourierLp hs u‖ ^ 2) := by
  rw [fourierSq_eq_eLpNorm_sq, ENNReal.ofReal_pow (norm_nonneg _)]
  congr 1
  rw [homogeneousFourierLp, Lp.norm_toLp,
    ENNReal.ofReal_toReal (memLp_homogeneousWeightedFourier_toL2Fun hs u).ne]

/-- The homogeneous norm is at most the inhomogeneous Bessel norm. -/
theorem norm_homogeneousFourierLp_le (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) :
    ‖homogeneousFourierLp hs u‖ ≤ ‖u‖ := by
  rw [← norm_fourier_toLp_eq u]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coeFn_homogeneousFourierLp hs u, coeFn_fourier_toLp hs u] with ξ hh hb
  rw [hh, hb, norm_homogeneousWeightedFourier, norm_besselSymbol_mul]
  exact mul_le_mul_of_nonneg_right (homogeneousWeight_le_besselWeight hs ξ) (norm_nonneg _)

/-- For orders at most two, the physical `L²` norm and the homogeneous norm together
control the Bessel norm. The `L²` term cannot be dropped at low frequencies. -/
theorem norm_le_toL2Fun_add_homogeneousFourierLp
    (hs : 0 ≤ s) (hs2 : s ≤ 2) (u : H^{s}(ℝ^n)) :
    ‖u‖ ≤ ‖toL2Fun hs u‖ + ‖homogeneousFourierLp hs u‖ := by
  let f := 𝓕 (toL2Fun hs u)
  let g := homogeneousFourierLp hs u
  let a := (Lp.memLp f).norm.toLp (fun ξ ↦ ‖f ξ‖)
  let b := (Lp.memLp g).norm.toLp (fun ξ ↦ ‖g ξ‖)
  have ha : ‖a‖ = ‖f‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable f), Lp.norm_def]
  have hb : ‖b‖ = ‖g‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable g), Lp.norm_def]
  calc
    ‖u‖ = ‖𝓕 (toLp u)‖ := (norm_fourier_toLp_eq u).symm
    _ ≤ ‖a + b‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [coeFn_fourier_toLp hs u, coeFn_homogeneousFourierLp hs u,
        Lp.coeFn_add a b, (Lp.memLp f).norm.coeFn_toLp, (Lp.memLp g).norm.coeFn_toLp]
        with ξ hB hG hab haξ hbξ
      rw [hab, Pi.add_apply]
      change ‖(𝓕 (toLp u)) ξ‖ ≤ ‖(Lp.memLp f).norm.toLp _ ξ + (Lp.memLp g).norm.toLp _ ξ‖
      rw [haξ, hbξ]
      change ‖(𝓕 (toLp u)) ξ‖ ≤ ‖‖(𝓕 (toL2Fun hs u)) ξ‖ + ‖g ξ‖‖
      rw [hB, show g ξ = homogeneousWeightedFourier s (toL2Fun hs u) ξ from hG,
        Real.norm_eq_abs, abs_of_nonneg (by positivity),
        norm_besselSymbol_mul, norm_homogeneousWeightedFourier]
      nlinarith [mul_le_mul_of_nonneg_right
        (besselWeight_le_one_add_homogeneousWeight hs hs2 ξ)
          (norm_nonneg ((𝓕 (toL2Fun hs u)) ξ))]
    _ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
    _ = ‖toL2Fun hs u‖ + ‖homogeneousFourierLp hs u‖ := by
      rw [ha, hb, Lp.norm_fourier_eq]

end SobolevSpace.Fractional
