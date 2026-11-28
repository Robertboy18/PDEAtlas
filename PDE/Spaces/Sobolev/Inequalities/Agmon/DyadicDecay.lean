/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import PDE.Spaces.Sobolev.Inequalities.Agmon.DyadicAnnulus
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import PDE.Analysis.MeasureTheory.Lp.Continuous
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Decay `O(|x|⁻²)` from weighted `L²` bounds

A `C²` function `u` on `ℝ³` such that `|x| u`, `|x|² ∇u` and `|x|² ∇²u` are square integrable
decays like `|x|⁻²`: for `|x| ≥ 2`,

`|u(x)| ≤ C (‖ |x| u ‖₂ + ‖ |x|² ∇u ‖₂^{1/2} ‖ |x|² ∇²u ‖₂^{1/2}) |x|⁻²`,

with a universal constant `C`. Hou, Wang and Yang draw this conclusion at the end of Step 3 of
the proof of their Proposition 4. They remark that more weighted bounds give
`∇ᵏu = O(|x|^{-5/2-k})` by the same argument; that is not formalized.

## Main results

* `lpNorm_sq_restrict_dyadicAnnulus_le`: `‖f‖²_{L²(A_R)} ≤ R^{-m} ∫ |x|^m |f|²` for every
  continuous `f` on `ℝ³`, every `m` and every `R > 0`, where `A_R = {R < |x| < 2R}`.
* `exists_norm_le_of_weighted_moments`: the bound above, for every `C²` function `u : ℝ³ → F`
  with values in a real normed space and with the three weighted bounds.
* `isBigO_inv_norm_sq_of_weighted_moments`: under the same hypotheses, `u = O(|x|⁻²)` at
  infinity.

## How it works

On `A_R` the weight `|x|^m` is at least `R^m`, so each weighted bound controls an `L²` norm over
`A_R`. Agmon's inequality on `A_R` (`exists_norm_le_dyadicAnnulus`) bounds `u` there by

`R^{-3/2} ‖u‖_{L²(A_R)} + ‖∇u‖_{L²(A_R)}^{1/2} ‖∇²u‖_{L²(A_R)}^{1/2}`,

with a constant that does not depend on `R`. With the three weighted bounds this is at most
`C (R^{-5/2} + R⁻²)`, hence `C R⁻²` for `R ≥ 1`. A point `x` with `|x| ≥ 2` lies in `A_R` for
`R = 2|x|/3`.

## References

* T. Y. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.1, Step 3 of the proof
  of Proposition 4. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace PDE.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **An `L²` norm on a dyadic annulus from a weighted integral.** On `A_R = {R < |x| < 2R}`
the weight `|x|^m` is at least `R^m`, so `‖f‖²_{L²(A_R)} ≤ R^{-m} ∫ |x|^m |f|²`. -/
theorem lpNorm_sq_restrict_dyadicAnnulus_le {G : Type*} [NormedAddCommGroup G] {f : ℝ^3 → G}
    (hf : Continuous f) {m : ℕ} (h : Integrable fun x ↦ ‖x‖ ^ m * ‖f x‖ ^ 2) {R : ℝ}
    (hR : 0 < R) :
    lpNorm f 2 (volume.restrict {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R}) ^ 2 ≤
      R⁻¹ ^ m * ∫ x, ‖x‖ ^ m * ‖f x‖ ^ 2 := by
  have hS : MeasurableSet {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R} :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hm : MemLp f 2 (volume.restrict {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R}) :=
    hf.continuousOn.memLp_of_subset_isCompact (isCompact_closedBall (0 : ℝ^3) (2 * R)) hS
      fun ξ hξ ↦ mem_closedBall_zero_iff.mpr hξ.2.le
  have hsq : lpNorm f 2 (volume.restrict {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R}) ^ 2 =
      ∫ z in {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R}, ‖f z‖ ^ 2 := by
    rw [MemLp.integral_sq_eq_lpNorm_sq hm.norm, ← toReal_eLpNorm, ← toReal_eLpNorm,
      eLpNorm_norm f hm.aestronglyMeasurable]
  have hw : Integrable fun x : ℝ^3 ↦ R⁻¹ ^ m * (‖x‖ ^ m * ‖f x‖ ^ 2) := h.const_mul _
  have hpt : ∀ z ∈ {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R},
      ‖f z‖ ^ 2 ≤ R⁻¹ ^ m * (‖z‖ ^ m * ‖f z‖ ^ 2) := fun z hz ↦ by
    have h1 : 1 ≤ R⁻¹ * ‖z‖ := by
      rw [inv_mul_eq_div, one_le_div hR]
      exact hz.1.le
    calc ‖f z‖ ^ 2 ≤ (R⁻¹ * ‖z‖) ^ m * ‖f z‖ ^ 2 :=
          le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ h1)
      _ = R⁻¹ ^ m * (‖z‖ ^ m * ‖f z‖ ^ 2) := by ring
  rw [hsq]
  calc ∫ z in {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R}, ‖f z‖ ^ 2
      ≤ ∫ z in {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R}, R⁻¹ ^ m * (‖z‖ ^ m * ‖f z‖ ^ 2) :=
        integral_mono_of_nonneg (.of_forall fun z ↦ sq_nonneg _) hw.restrict
          (ae_restrict_of_forall_mem hS hpt)
    _ ≤ ∫ z, R⁻¹ ^ m * (‖z‖ ^ m * ‖f z‖ ^ 2) :=
        setIntegral_le_integral hw (.of_forall fun z ↦ by positivity)
    _ = R⁻¹ ^ m * ∫ x, ‖x‖ ^ m * ‖f x‖ ^ 2 := integral_const_mul _ _

/-- **Decay from weighted bounds.** There is a constant `C` such that every `C²` function
`u : ℝ³ → F` with `|x| u`, `|x|² ∇u` and `|x|² ∇²u` square integrable satisfies, for `|x| ≥ 2`,

`|u(x)| ≤ C (‖ |x| u ‖₂ + ‖ |x|² ∇u ‖₂^{1/2} ‖ |x|² ∇²u ‖₂^{1/2}) |x|⁻²`.

The proof applies Agmon's inequality on the annulus `R < |ξ| < 2R` with `R = 2|x|/3`, where
the weights are at least `R` and `R²`. -/
theorem exists_norm_le_of_weighted_moments :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ^3 → F, ContDiff ℝ 2 u →
      Integrable (fun x ↦ ‖x‖ ^ 2 * ‖u x‖ ^ 2) →
      Integrable (fun x ↦ ‖x‖ ^ 4 * ‖fderiv ℝ u x‖ ^ 2) →
      Integrable (fun x ↦ ‖x‖ ^ 4 * ‖fderiv ℝ (fderiv ℝ u) x‖ ^ 2) →
      ∀ x : ℝ^3, 2 ≤ ‖x‖ →
        ‖u x‖ ≤ C * (√(∫ y, ‖y‖ ^ 2 * ‖u y‖ ^ 2) +
          √(√(∫ y, ‖y‖ ^ 4 * ‖fderiv ℝ u y‖ ^ 2) *
            √(∫ y, ‖y‖ ^ 4 * ‖fderiv ℝ (fderiv ℝ u) y‖ ^ 2))) * ‖x‖⁻¹ ^ 2 := by
  obtain ⟨C, hC, hA⟩ := exists_norm_le_dyadicAnnulus (F := F)
  refine ⟨9 / 4 * C, by positivity, fun u hu h0 h1 h2 x hx ↦ ?_⟩
  have hx0 : 0 < ‖x‖ := by linarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 / 3 * ‖x‖ := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hRdef]; positivity
  have hR1 : 1 ≤ R := by rw [hRdef]; linarith
  have ht0 : 0 < R⁻¹ := inv_pos.mpr hR0
  have hu1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have key := hA R hR0 u hu x (by rw [hRdef]; linarith) (by rw [hRdef]; linarith)
  -- The three norms on the annulus, from the weighted bounds.
  have hN0 := lpNorm_sq_restrict_dyadicAnnulus_le hu.continuous h0 hR0
  have hN1 := lpNorm_sq_restrict_dyadicAnnulus_le (hu.continuous_fderiv (by norm_num)) h1 hR0
  have hN2 := lpNorm_sq_restrict_dyadicAnnulus_le (hu1.continuous_fderiv one_ne_zero) h2 hR0
  have hM0 : 0 ≤ ∫ y, ‖y‖ ^ 2 * ‖u y‖ ^ 2 := integral_nonneg fun y ↦ by positivity
  have hM1 : 0 ≤ ∫ y, ‖y‖ ^ 4 * ‖fderiv ℝ u y‖ ^ 2 := integral_nonneg fun y ↦ by positivity
  have hM2 : 0 ≤ ∫ y, ‖y‖ ^ 4 * ‖fderiv ℝ (fderiv ℝ u) y‖ ^ 2 :=
    integral_nonneg fun y ↦ by positivity
  have hN0nn : 0 ≤ lpNorm u 2 (volume.restrict {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R}) :=
    lpNorm_nonneg
  have hN1nn : 0 ≤ lpNorm (fderiv ℝ u) 2
      (volume.restrict {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R}) := lpNorm_nonneg
  generalize (∫ y, ‖y‖ ^ 2 * ‖u y‖ ^ 2) = M₀ at hN0 hM0 ⊢
  generalize (∫ y, ‖y‖ ^ 4 * ‖fderiv ℝ u y‖ ^ 2) = M₁ at hN1 hM1 ⊢
  generalize (∫ y, ‖y‖ ^ 4 * ‖fderiv ℝ (fderiv ℝ u) y‖ ^ 2) = M₂ at hN2 hM2 ⊢
  generalize lpNorm u 2 (volume.restrict {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R}) = N₀
    at hN0 hN0nn key
  generalize lpNorm (fderiv ℝ u) 2 (volume.restrict {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R}) = N₁
    at hN1 hN1nn key
  generalize lpNorm (fderiv ℝ (fderiv ℝ u)) 2
    (volume.restrict {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R}) = N₂ at hN2 key
  -- `R^{-3/2} N₀ ≤ R⁻² √M₀`.
  have hN0' : N₀ ≤ R⁻¹ * √M₀ := by
    by_contra hcon
    have hsq : (R⁻¹ * √M₀) ^ 2 < N₀ ^ 2 :=
      pow_lt_pow_left₀ (not_le.mp hcon) (by positivity) two_ne_zero
    rw [mul_pow, Real.sq_sqrt hM0] at hsq
    linarith
  have hpow : R ^ (-(3 / 2) : ℝ) ≤ R⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  have hA0 : R ^ (-(3 / 2) : ℝ) * N₀ ≤ R⁻¹ ^ 2 * √M₀ := by
    calc R ^ (-(3 / 2) : ℝ) * N₀ ≤ R⁻¹ * (R⁻¹ * √M₀) :=
          mul_le_mul hpow hN0' hN0nn ht0.le
      _ = R⁻¹ ^ 2 * √M₀ := by ring
  -- `N₁ N₂ ≤ R⁻⁴ √M₁ √M₂`.
  have hA12 : N₁ * N₂ ≤ R⁻¹ ^ 4 * (√M₁ * √M₂) := by
    by_contra hcon
    have hsq : (R⁻¹ ^ 4 * (√M₁ * √M₂)) ^ 2 < (N₁ * N₂) ^ 2 :=
      pow_lt_pow_left₀ (not_le.mp hcon) (by positivity) two_ne_zero
    have e : (R⁻¹ ^ 4 * (√M₁ * √M₂)) ^ 2 = R⁻¹ ^ 4 * M₁ * (R⁻¹ ^ 4 * M₂) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hM1, Real.sq_sqrt hM2]
      ring
    have hprod : N₁ ^ 2 * N₂ ^ 2 ≤ R⁻¹ ^ 4 * M₁ * (R⁻¹ ^ 4 * M₂) :=
      mul_le_mul hN1 hN2 (sq_nonneg _) (by positivity)
    have e3 : (N₁ * N₂) ^ 2 = N₁ ^ 2 * N₂ ^ 2 := by ring
    linarith
  have hB : √N₁ * √N₂ ≤ R⁻¹ ^ 2 * √(√M₁ * √M₂) := by
    have e : √(R⁻¹ ^ 4 * (√M₁ * √M₂)) = R⁻¹ ^ 2 * √(√M₁ * √M₂) := by
      rw [Real.sqrt_mul (by positivity), show R⁻¹ ^ 4 = (R⁻¹ ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [← Real.sqrt_mul hN1nn, ← e]
    exact Real.sqrt_le_sqrt hA12
  have ht : R⁻¹ ^ 2 = 9 / 4 * ‖x‖⁻¹ ^ 2 := by
    rw [hRdef, mul_inv, mul_pow]
    norm_num
  calc ‖u x‖ ≤ C * (R ^ (-(3 / 2) : ℝ) * N₀ + √N₁ * √N₂) := key
    _ ≤ C * (R⁻¹ ^ 2 * √M₀ + R⁻¹ ^ 2 * √(√M₁ * √M₂)) :=
        mul_le_mul_of_nonneg_left (add_le_add hA0 hB) hC
    _ = 9 / 4 * C * (√M₀ + √(√M₁ * √M₂)) * ‖x‖⁻¹ ^ 2 := by
        rw [ht]
        ring

/-- **`u = O(|x|⁻²)` at infinity** for a `C²` function `u : ℝ³ → F` with `|x| u`, `|x|² ∇u` and
`|x|² ∇²u` square integrable. -/
theorem isBigO_inv_norm_sq_of_weighted_moments {u : ℝ^3 → F} (hu : ContDiff ℝ 2 u)
    (h0 : Integrable fun x ↦ ‖x‖ ^ 2 * ‖u x‖ ^ 2)
    (h1 : Integrable fun x ↦ ‖x‖ ^ 4 * ‖fderiv ℝ u x‖ ^ 2)
    (h2 : Integrable fun x ↦ ‖x‖ ^ 4 * ‖fderiv ℝ (fderiv ℝ u) x‖ ^ 2) :
    u =O[cocompact (ℝ^3)] fun x ↦ ‖x‖⁻¹ ^ 2 := by
  obtain ⟨C, -, hC⟩ := exists_norm_le_of_weighted_moments (F := F)
  refine IsBigO.of_bound (C * (√(∫ y, ‖y‖ ^ 2 * ‖u y‖ ^ 2) +
    √(√(∫ y, ‖y‖ ^ 4 * ‖fderiv ℝ u y‖ ^ 2) *
      √(∫ y, ‖y‖ ^ 4 * ‖fderiv ℝ (fderiv ℝ u) y‖ ^ 2)))) ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop 2] with x hx
  have h := hC u hu h0 h1 h2 x hx
  rwa [Real.norm_of_nonneg (by positivity)]

end PDE.Analysis
