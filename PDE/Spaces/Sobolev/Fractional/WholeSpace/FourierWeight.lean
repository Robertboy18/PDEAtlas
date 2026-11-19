/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TemperedDistribution.Lp
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.L2Representative
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Plancherel
import PDE.Spaces.Sobolev.Fractional.WholeSpace.Embedding

/-!
# Fourier representatives and integer weights

Mathlib's Bessel condition is equivalent to square integrability of the weighted
Fourier representative. At integer order, the Bessel weight and `1 + ‖ξ‖^k` are
comparable, including order zero.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.5, Theorem 8, (19)-(20), p. 297.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution BesselPotentialSpace
open scoped BesselPotentialSpace FourierTransform SchwartzMap

namespace SobolevSpace.Fractional

variable {n : ℕ}

/-- The Bessel distribution condition is square integrability of the weighted transform. -/
theorem memSobolev_iff_memLp_besselWeight (s : ℝ)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    MemSobolev s 2 (u : 𝓢'(ℝ^n, ℂ)) ↔
      MemLp (fun ξ ↦ besselSymbol n s ξ * (𝓕 u) ξ) 2 volume := by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier, Lp.fourier_toTemperedDistribution_eq]
  constructor
  · rintro ⟨v, hv⟩
    exact (memLp_congr_ae
      ((Lp.smulLeft_toTemperedDistribution_eq_iff besselSymbol_hasTemperateGrowth).mp hv)).mpr
      (Lp.memLp v)
  · intro hu
    exact ⟨hu.toLp _, (Lp.smulLeft_toTemperedDistribution_eq_iff
      besselSymbol_hasTemperateGrowth).mpr hu.coeFn_toLp.symm⟩

/-- The Fourier representative of the Bessel transform is the weighted physical transform. -/
theorem coeFn_fourier_toLp {s : ℝ} (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) :
    (𝓕 (toLp u) : Lp ℂ 2 (volume : Measure (ℝ^n))) =ᵐ[volume]
      fun ξ ↦ besselSymbol n s ξ * (𝓕 (toL2Fun hs u)) ξ := by
  have h := smulLeftCLM_fourier_toDist u
  rw [toDistr_eq_toL2Fun hs, Lp.fourier_toTemperedDistribution_eq] at h
  exact ((Lp.smulLeft_toTemperedDistribution_eq_iff besselSymbol_hasTemperateGrowth).mp h).symm

private theorem rpow_sq_half_nat {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    (r ^ 2) ^ ((k : ℝ) / 2) = r ^ k := by
  rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr]
  rw [show ((2 : ℕ) : ℝ) * ((k : ℝ) / 2) = (k : ℝ) by ring, Real.rpow_natCast]

/-- The integer weight is at most twice the Bessel weight. -/
theorem one_add_norm_pow_le_besselWeight (k : ℕ) (ξ : ℝ^n) :
    1 + ‖ξ‖ ^ k ≤ 2 * (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) := by
  have h1 : (1 : ℝ) ≤ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) :=
    Real.one_le_rpow (by linarith [sq_nonneg ‖ξ‖]) (by positivity)
  have hr : ‖ξ‖ ^ k ≤ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) := by
    rw [← rpow_sq_half_nat (norm_nonneg ξ) k]
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  linarith

/-- The Bessel weight is bounded by a constant times the integer weight. -/
theorem besselWeight_le_one_add_norm_pow (k : ℕ) (ξ : ℝ^n) :
    (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) ≤ 2 ^ k * (1 + ‖ξ‖ ^ k) := by
  have hfirst : (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) ≤ (1 + ‖ξ‖) ^ k := by
    rw [← rpow_sq_half_nat (by positivity : 0 ≤ 1 + ‖ξ‖) k]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith [norm_nonneg ξ]) (by positivity)
  apply hfirst.trans
  by_cases h : ‖ξ‖ ≤ 1
  · calc
      _ ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ ≤ 2 ^ k * (1 + ‖ξ‖ ^ k) :=
        le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg (norm_nonneg ξ) k])
  · have h' : 1 ≤ ‖ξ‖ := le_of_lt (lt_of_not_ge h)
    calc
      _ ≤ (2 * ‖ξ‖) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * ‖ξ‖ ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + ‖ξ‖ ^ k) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The weighted transform `ξ ↦ (1 + ‖ξ‖^k) 𝓕u(ξ)` of `u ∈ L²(ℝ^n)`, the function in condition
(19) of Evans §5.8.5, Theorem 8. -/
def integerWeightedFourier (k : ℕ) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    ℝ^n → ℂ :=
  fun ξ ↦ ((1 + ‖ξ‖ ^ k : ℝ) : ℂ) * (𝓕 u) ξ

theorem norm_integerWeightedFourier_le (k : ℕ)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n))) (ξ : ℝ^n) :
    ‖integerWeightedFourier k u ξ‖ ≤ 2 * ‖besselSymbol n (k : ℝ) ξ * (𝓕 u) ξ‖ := by
  simp only [integerWeightedFourier, besselSymbol, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖ ^ k),
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖ ^ 2) _)]
  nlinarith [mul_le_mul_of_nonneg_right (one_add_norm_pow_le_besselWeight k ξ)
    (norm_nonneg ((𝓕 u) ξ))]

theorem norm_besselWeight_mul_fourier_le_integerWeightedFourier (k : ℕ)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n))) (ξ : ℝ^n) :
    ‖besselSymbol n (k : ℝ) ξ * (𝓕 u) ξ‖ ≤ 2 ^ k * ‖integerWeightedFourier k u ξ‖ := by
  simp only [integerWeightedFourier, besselSymbol, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖ ^ k),
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖ ^ 2) _)]
  nlinarith [mul_le_mul_of_nonneg_right (besselWeight_le_one_add_norm_pow k ξ)
    (norm_nonneg ((𝓕 u) ξ))]

/-- At integer order the literal weight `1 + ‖ξ‖^k` characterizes Bessel membership. -/
theorem memSobolev_iff_memLp_integerWeightedFourier (k : ℕ)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    MemSobolev (k : ℝ) 2 (u : 𝓢'(ℝ^n, ℂ)) ↔
      MemLp (integerWeightedFourier k u) 2 volume := by
  rw [memSobolev_iff_memLp_besselWeight]
  constructor
  · intro h
    apply h.of_le_mul (c := 2)
    · exact (by fun_prop : Continuous (fun ξ : ℝ^n ↦
        ((1 + ‖ξ‖ ^ k : ℝ) : ℂ))).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)
    · exact Filter.Eventually.of_forall (norm_integerWeightedFourier_le k u)
  · intro h
    apply h.of_le_mul (c := 2 ^ k)
    · exact besselSymbol_hasTemperateGrowth.1.continuous.aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable _)
    · exact Filter.Eventually.of_forall
        (norm_besselWeight_mul_fourier_le_integerWeightedFourier k u)

/-- The weighted Fourier representative of a Bessel element, as an `L²` class. -/
def integerWeightedFourierLp {k : ℕ} (u : H^{(k : ℝ)}(ℝ^n)) :
    Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  ((memSobolev_iff_memLp_integerWeightedFourier k (toL2Fun (Nat.cast_nonneg k) u)).mp
    (by rw [← toDistr_eq_toL2Fun]; exact u.memSobolev_toDistr)).toLp _

theorem coeFn_integerWeightedFourierLp {k : ℕ} (u : H^{(k : ℝ)}(ℝ^n)) :
    (integerWeightedFourierLp u : ℝ^n → ℂ) =ᵐ[volume]
      integerWeightedFourier k (toL2Fun (Nat.cast_nonneg k) u) :=
  MemLp.coeFn_toLp _

/-- The literal integer Fourier norm is bounded by twice the Bessel norm. -/
theorem norm_integerWeightedFourierLp_le {k : ℕ} (u : H^{(k : ℝ)}(ℝ^n)) :
    ‖integerWeightedFourierLp u‖ ≤ 2 * ‖u‖ := by
  rw [← norm_fourier_toLp_eq u]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coeFn_integerWeightedFourierLp u,
    coeFn_fourier_toLp (Nat.cast_nonneg k) u] with ξ hu hv
  rw [hu, hv]
  exact norm_integerWeightedFourier_le k _ ξ

/-- The literal integer Fourier norm controls the Bessel norm. -/
theorem norm_le_integerWeightedFourierLp {k : ℕ} (u : H^{(k : ℝ)}(ℝ^n)) :
    ‖u‖ ≤ 2 ^ k * ‖integerWeightedFourierLp u‖ := by
  rw [← norm_fourier_toLp_eq u]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coeFn_integerWeightedFourierLp u,
    coeFn_fourier_toLp (Nat.cast_nonneg k) u] with ξ hu hv
  rw [hu, hv]
  exact norm_besselWeight_mul_fourier_le_integerWeightedFourier k _ ξ

end SobolevSpace.Fractional
