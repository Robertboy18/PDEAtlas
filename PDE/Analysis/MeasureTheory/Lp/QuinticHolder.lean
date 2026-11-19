/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralPower
public import PDE.Analysis.MeasureTheory.Lp.SectionNorm
import PDE.Analysis.ENNReal.Holder

/-!
# Hölder estimates for quintic products

Hölder's inequality with exponents 3, 6 and 2 gives `‖u⁴ v‖_{L²} ≤ ‖u‖_{L¹²}⁴ ‖v‖_{L⁶}` for a
real function `u` and a vector field `v`. Integrating in time gives the critical
`L⁴_t L¹²_x` estimate and the integrability of the forcing. With `v = Du` these are the
estimates of `‖u⁴ Du‖_{L²}` in step 2 of the proof of Evans, §12.4, Theorem 3; with `v = u`
they give the bound `‖u⁵‖_{L²} ≤ ‖u‖_{L⁶} ‖u‖_{L¹²}⁴` of step 4, which Evans obtains from an
interpolation inequality. The measures are arbitrary, so the estimates also hold on the balls
`B(x₀, T - t)` of step 4.

## Main results

* `eLpNorm_pow_four`, `MemLp.pow_four_smul`, `lpNorm_pow_four_smul_le`: the spatial estimate.
* `integrable_lpNorm_pow_four_smul`, `integral_lpNorm_pow_four_smul_le`: its time integral,
  bounded by the fourth power of the `L⁴_t L¹²_x` norm of `u` times a uniform `L⁶` bound on `v`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 3, the estimate of `‖u⁴ Du‖_{L²}` in
  step 2 of its proof, p. 684, and the estimate of `‖u⁵‖_{L²}` in step 4, p. 685.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} {u : X → ℝ} {v : X → E}

/-- The `L³` seminorm of `u⁴` is the fourth power of the `L¹²` seminorm of `u`. -/
theorem eLpNorm_pow_four (hu : AEStronglyMeasurable u μ) :
    eLpNorm (fun x ↦ u x ^ 4) 3 μ = eLpNorm u 12 μ ^ 4 := by
  have h := eLpNorm_norm_rpow (p := (3 : ℝ≥0∞)) u hu (by norm_num : (0 : ℝ) < 4)
  norm_num only [ENNReal.ofReal_ofNat, Real.rpow_ofNat,
    ENNReal.rpow_ofNat] at h
  simpa only [Real.norm_eq_abs, (by decide : Even (4 : ℕ)).pow_abs] using h

/-- The quartic multiplier sends an L6 vector field into L2. -/
theorem MemLp.pow_four_smul (hu : MemLp u 12 μ) (hv : MemLp v 6 μ) :
    MemLp (fun x ↦ u x ^ 4 • v x) 2 μ := by
  let : ENNReal.HolderTriple (3 : ℝ≥0∞) 6 2 := by
    convert ENNReal.holderTriple_div_ofReal (p := 6) (r := 3)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num [ENNReal.eq_div_iff]
  have hu4 : MemLp (fun x ↦ u x ^ 4) 3 μ := by
    rw [memLp_iff, eLpNorm_pow_four hu.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hu.eLpNorm_lt_top
  exact hu4.smul hv

/-- Hölder's inequality `‖u⁴ v‖_{L²} ≤ ‖u‖_{L¹²}⁴ ‖v‖_{L⁶}`, at the exponents of the critical
quintic wave equation. -/
theorem lpNorm_pow_four_smul_le (hu : MemLp u 12 μ) (hv : MemLp v 6 μ) :
    lpNorm (fun x ↦ u x ^ 4 • v x) 2 μ ≤ lpNorm u 12 μ ^ 4 * lpNorm v 6 μ := by
  let : ENNReal.HolderTriple (3 : ℝ≥0∞) 6 2 := by
    convert ENNReal.holderTriple_div_ofReal (p := 6) (r := 3)
      (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num [ENNReal.eq_div_iff]
  have h := eLpNorm_smul_le_mul_eLpNorm (p := (3 : ℝ≥0∞)) (q := 6) (r := 2)
    (hu.aestronglyMeasurable.pow 4) hv.aestronglyMeasurable
  change eLpNorm (fun x ↦ u x ^ 4 • v x) 2 μ ≤
    eLpNorm (fun x ↦ u x ^ 4) 3 μ * eLpNorm v 6 μ at h
  rw [eLpNorm_pow_four hu.aestronglyMeasurable] at h
  simpa only [← toReal_eLpNorm, ENNReal.toReal_mul, ENNReal.toReal_pow] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top hu.eLpNorm_ne_top)
      hv.eLpNorm_ne_top) h

variable {S X E : Type*} [MeasurableSpace S] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {μ : Measure S} {ν : Measure X} [SFinite ν]
  {u : S × X → ℝ} {v : S × X → E} {M : ℝ}

/-- A bounded L6 field multiplied by a critical L4-time/L12-space quartic field
has time-integrable L2 sections. Section membership prevents totalized norms from
hiding spatial nonintegrability. -/
theorem integrable_lpNorm_pow_four_smul
    (hu : Measurable u) (hv : Measurable v)
    (hu12 : ∀ᵐ t ∂μ, MemLp (fun x ↦ u (t, x)) 12 ν)
    (hv6 : ∀ᵐ t ∂μ, MemLp (fun x ↦ v (t, x)) 6 ν)
    (hM : ∀ᵐ t ∂μ, lpNorm (fun x ↦ v (t, x)) 6 ν ≤ M)
    (hu4 : MemLp (fun t ↦ lpNorm (fun x ↦ u (t, x)) 12 ν) 4 μ) :
    Integrable (fun t ↦ lpNorm (fun x ↦ u (t, x) ^ 4 • v (t, x)) 2 ν) μ := by
  have hp := hu4.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  simp only [Real.norm_of_nonneg lpNorm_nonneg] at hp
  apply (hp.mul_const M).mono'
    (((hu.pow_const 4).smul hv).eLpNorm_prod_right (p := 2) (ν := ν)
      (by norm_num) (by norm_num)).ennreal_toReal.aestronglyMeasurable
  filter_upwards [hu12, hv6, hM] with t hut hvt ht
  change ‖lpNorm (fun x ↦ u (t, x) ^ 4 • v (t, x)) 2 ν‖ ≤ _
  rw [Real.norm_of_nonneg lpNorm_nonneg]
  exact (lpNorm_pow_four_smul_le hut hvt).trans
    (mul_le_mul_of_nonneg_left ht (pow_nonneg lpNorm_nonneg 4))

/-- The time integral of `‖u⁴ v‖_{L²}` is bounded by the fourth power of the `L⁴_t L¹²_x`
norm of `u` times the uniform `L⁶` bound `M` on `v`. Both measures are arbitrary. -/
theorem integral_lpNorm_pow_four_smul_le
    (hu : Measurable u) (hv : Measurable v)
    (hu12 : ∀ᵐ t ∂μ, MemLp (fun x ↦ u (t, x)) 12 ν)
    (hv6 : ∀ᵐ t ∂μ, MemLp (fun x ↦ v (t, x)) 6 ν)
    (hM : ∀ᵐ t ∂μ, lpNorm (fun x ↦ v (t, x)) 6 ν ≤ M)
    (hu4 : MemLp (fun t ↦ lpNorm (fun x ↦ u (t, x)) 12 ν) 4 μ) :
    ∫ t, lpNorm (fun x ↦ u (t, x) ^ 4 • v (t, x)) 2 ν ∂μ ≤
      lpNorm (fun t ↦ lpNorm (fun x ↦ u (t, x)) 12 ν) 4 μ ^ 4 * M := by
  have hp := hu4.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  simp only [Real.norm_of_nonneg lpNorm_nonneg] at hp
  calc
    _ ≤ ∫ t, lpNorm (fun x ↦ u (t, x)) 12 ν ^ 4 * M ∂μ := by
      apply integral_mono_ae (integrable_lpNorm_pow_four_smul hu hv hu12 hv6 hM hu4)
        (hp.mul_const M)
      filter_upwards [hu12, hv6, hM] with t hut hvt ht
      exact (lpNorm_pow_four_smul_le hut hvt).trans
        (mul_le_mul_of_nonneg_left ht (pow_nonneg lpNorm_nonneg 4))
    _ = _ := by
      rw [integral_mul_const]
      congr 1
      simpa only [Real.norm_of_nonneg lpNorm_nonneg, Nat.cast_ofNat] using
        integral_norm_pow_eq_lpNorm_pow hu4.aestronglyMeasurable (by norm_num : 0 < (4 : ℕ))

end MeasureTheory
