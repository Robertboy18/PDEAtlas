/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearCostTails

/-!
# Envelopes of the constants of the horizontal estimate of `u_y`

The constant `C₂(τ)` of Chen and Hou, Part I, Lemma 3.4 (`shearConstant`) is a supremum over
`h > 0` and `B ≥ 4` of the localized integrals `S̃_{1D}(B, A)`, `S_up(B, A)` and `S_out(B, h)`,
`A = min(h, B)`. Each of them is bounded by an integral that does not depend on `B`.

* `S_up(B, A) ≤ U(A) = 4 ∫_0^A ∫_{p > 0} |Δ| |t - T|^{1/2}` for `A ≤ B`. Inside the boxes the
  localized and the full columns agree. Near the edge, `B - 1 < p ≤ B + 1`, the localized kernel
  `-K₂(p - 1, t)` is at most `Δ(p, t)` above `t = p - 1`, and its map `(p - 1)²/t` lies between
  `T(p, t)` and `t`.
* `S_out(B, h) ≤ 2 (2h)^{1/2} W(h)` with `W(h) = ∫_h^∞ ∫_{p > 0} |Δ|`. On each row `0 < t ≤ B`
  the localized and the full kernels have the same mass over `p > 0`, and the positive part of
  the localized kernel is the smaller one.
* `S̃_{1D}(B, A) ≤ X(A) = ∫_0^∞ (2p)^{1/2} (g_A(p - 1) - g_A(p + 1)) dp` with
  `g_A(y) = A/(y² + A²)`. The two differ by
  `∫_B^∞ ((2(y + 1))^{1/2} - (2(y - 1))^{1/2}) g_A(y) dy ≥ 0`.

The mass envelope has the closed form `X(A) = √2 π / (√(1 + A²) + A)^{1/2}`. With `p = u²` and
`β = √(1 + A²)`, the quartics `(u² ∓ 1)² + A²` factor as `(u² - γu + β)(u² + γu + β)` with
`γ² = 2β ± 2`, and the partial fractions have explicit primitives in logarithms and arctangents.
Hence `C₂(τ)` is at most the supremum over `A > 0` of
`(X(A) + τ (U(A) + 2 (2A)^{1/2} W(A))) / √2`.

## Main definitions

* `shearUpperEnvelope`: the upper envelope `U(A)`.
* `shearOuterMass`: the mass `W(h)` above the height `h`.
* `shearMassEnvelope`: the mass envelope `X(A)`.
* `shearHolderEnvelope`: the envelope `X(A) + τ (U(A) + 2 (2A)^{1/2} W(A))`.

## Main results

* `shearUpperCost_le_envelope`: `S_up(B, A) ≤ U(A)` for `A ≤ B`.
* `shearOuterCost_le_envelope`: `S_out(B, h) ≤ 2 (2h)^{1/2} W(h)`.
* `shearMassCost_le_envelope`: `S̃_{1D}(B, A) ≤ X(A)`.
* `shearMassEnvelope_eq`: `X(A) = √2 π / (√(1 + A²) + A)^{1/2}` for `A > 0`.
* `shearConstant_le_iSup_envelope`:
  `C₂(τ) ≤ sup_{A > 0} (X(A) + τ (U(A) + 2 (2A)^{1/2} W(A))) / √2`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Lemma 3.4, pp. 28-29, and
  Appendix B.1, (B.40), pp. 129-136.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace IncompressibleFlow.SharpHolder

/-- The full upper envelope `U(A) = 4 ∫_0^A ∫_{p > 0}` of the transport density. -/
def shearUpperEnvelope (A : ℝ) : ℝ≥0∞ :=
  4 * ∫⁻ t in Ioc 0 A, ∫⁻ p in Ioi 0, shearColumnDensity p t

/-- The mass `W(h) = ∫_h^∞ ∫_{p > 0} |Δ|` above the height `h`. -/
def shearOuterMass (h : ℝ) : ℝ≥0∞ := ∫⁻ t in Ioi h, ∫⁻ p in Ioi 0, ‖shearDifference p t‖ₑ

/-- The mass envelope `X(A) = ∫_0^∞ (2p)^{1/2} (g_A(p - 1) - g_A(p + 1)) dp`,
`g_A(y) = A/(y² + A²)`. -/
def shearMassEnvelope (A : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in Ioi 0, ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) *
    (A / ((p - 1) ^ 2 + A ^ 2) - A / ((p + 1) ^ 2 + A ^ 2)))

/-! ### The upper cost -/

/-- Where `Q ≤ 0`, `s_c(p) ≤ t`. -/
theorem shearThreshold_le_of_shearQuartic_nonpos {p t : ℝ} (ht : 0 ≤ t)
    (h : shearQuartic p t ≤ 0) : shearThreshold p ≤ t := by
  rw [shearQuartic_eq_threshold] at h
  have hw := Real.sqrt_nonneg (p ^ 4 - p ^ 2 + 1)
  have ha : 0 < t ^ 2 - (-(p ^ 2 + 1) - 2 * Real.sqrt (p ^ 4 - p ^ 2 + 1)) / 3 := by
    linarith [sq_nonneg t, sq_nonneg p]
  have hle : shearThreshold p ^ 2 ≤ t ^ 2 := by
    by_contra hc
    push Not at hc
    have := mul_pos (sub_pos.2 hc) ha
    linarith
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) ht two_ne_zero).1 hle

/-- Each column of the localized upper cost is at most the column `∫_0^A` of the transport
density, for `A ≤ B`. -/
theorem shearCost_le_lintegral_shearColumnDensity {B A p : ℝ} (hB : 4 ≤ B) (hAB : A ≤ B)
    (hp : 0 < p) : shearCost B A p ≤ ∫⁻ t in Ioc 0 A, shearColumnDensity p t := by
  rcases le_or_gt (p + 1) B with h₁ | h₁
  · have hpB : |p| + 1 ≤ B := by rwa [abs_of_pos hp]
    have hs : 0 ≤ shearThreshold p := Real.sqrt_nonneg _
    calc shearCost B A p
        = ∫⁻ t in Ioc (shearThreshold p) A, shearColumnDensity p t := by
          rw [shearCost, localShearThreshold, ite_eq_left hpB]
          refine setLIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
          rw [localShearMap, ite_eq_left hpB, localShearDifference_of_le hpB, shearColumnDensity,
            indicator_of_mem (show t ∈ Ioi (shearThreshold p) from ht.1)]
      _ ≤ _ := lintegral_mono_set (Ioc_subset_Ioc_left hs)
  rcases le_or_gt p (B + 1) with h₂ | h₂
  · have hpB : ¬|p| + 1 ≤ B := by rw [abs_of_pos hp]; linarith
    have ha : 0 < p - 1 := by linarith
    have hQ : shearQuartic p (p - 1) ≤ 0 := by
      have e : shearQuartic p (p - 1) = -4 * (p - 1) ^ 4 := by simp only [shearQuartic]; ring
      rw [e]
      have := pow_nonneg ha.le 4
      linarith
    have hsc := shearThreshold_le_of_shearQuartic_nonpos ha.le hQ
    calc shearCost B A p
        ≤ ∫⁻ t in Ioc (p - 1) A, shearColumnDensity p t := by
          rw [shearCost, localShearThreshold, ite_eq_right hpB, abs_of_pos hp]
          refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
          have ht0 : 0 < t := ha.trans ht.1
          have htp : t < p + 1 := by linarith [ht.2]
          rw [localShearMap, ite_eq_right hpB, abs_of_pos hp,
            localShearDifference_of_lt (by linarith) h₁ h₂, shearColumnDensity,
            indicator_of_mem (show t ∈ Ioi (shearThreshold p) from hsc.trans_lt ht.1)]
          have hK₁ : shearDensity (p - 1) t ≤ 0 := by
            rw [shearDensity_eq]
            exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [ht.1]) (by positivity)
          have hK₂ : 0 ≤ shearDensity (p + 1) t := by
            rw [shearDensity_eq]
            exact div_nonneg (by nlinarith) (by positivity)
          have hΔ : -shearDensity (p - 1) t ≤ shearDifference p t := by
            rw [shearDifference]; linarith
          have hT : shearMap p t ≤ (p - 1) ^ 2 / t := by
            refine shearMap_le_of_shearCubic_nonneg ht0 (by positivity) ?_
            have e := mul_shearCubic_eq p ht0.ne' ((p - 1) ^ 2 / t)
            have e' : t * shearCubic p t ((p - 1) ^ 2 / t) =
                (p - 1) ^ 2 * ((p - 1) ^ 2 + t ^ 2) ^ 2 / t ^ 2 := by
              rw [e]
              field_simp
              ring
            exact (mul_nonneg_iff_of_pos_left ht0).1 (by rw [e']; positivity)
          have hT0 := shearMap_nonneg (y₁ := p) ht0
          have hat : (p - 1) ^ 2 / t ≤ t := by
            rw [div_le_iff₀ ht0]
            nlinarith [ht.1]
          refine mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _) ?_
            (by norm_num)))
          · rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
            exact hΔ
          · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
            linarith
      _ ≤ _ := lintegral_mono_set (Ioc_subset_Ioc_left ha.le)
  · simp only [shearCost, localShearDifference_of_gt h₂, enorm_zero, zero_mul, lintegral_const,
      zero_le]

/-- `S_up(B, A) ≤ U(A)` for `A ≤ B`. -/
theorem shearUpperCost_le_envelope {B A : ℝ} (hB : 4 ≤ B) (hAB : A ≤ B) :
    shearUpperCost B A ≤ shearUpperEnvelope A := by
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (Ioc 0 A)) (f := fun p t ↦ shearColumnDensity p t)
    measurable_shearColumnDensity.aemeasurable
  rw [shearUpperCost, shearUpperEnvelope, ← hswap]
  gcongr 4 * ?_
  exact setLIntegral_mono' measurableSet_Ioi fun p hp ↦
    shearCost_le_lintegral_shearColumnDensity hB hAB hp

/-! ### The outer cost -/

/-- For `t > 0`, `p ↦ K₂(p + e, t)` is integrable on the line. -/
theorem integrable_shearDensity_add {t : ℝ} (ht : 0 < t) (e : ℝ) :
    Integrable fun p ↦ shearDensity (p + e) t := by
  have hk : Integrable fun p : ℝ ↦ 1 / (2 * ((p + e) ^ 2 + t ^ 2)) := by
    refine (((integrable_inv_one_add_sq.comp_div ht.ne').comp_add_right e).const_mul
      (1 / (2 * t ^ 2))).congr (Eventually.of_forall fun p ↦ ?_)
    simp only
    field_simp
    ring
  have hm : Measurable fun p ↦ shearDensity (p + e) t := by
    simp only [shearDensity_eq]
    fun_prop
  exact hk.mono' hm.aestronglyMeasurable (Eventually.of_forall fun p ↦ by
    rw [Real.norm_eq_abs]
    exact abs_shearDensity_le _ _)

/-- `∫_c^∞ K₂(p + e, t) dp = (c + e)/(2((c + e)² + t²))` for `t > 0`. -/
theorem integral_Ioi_shearDensity_add {t : ℝ} (ht : 0 < t) (c e : ℝ) :
    ∫ p in Ioi c, shearDensity (p + e) t = (c + e) / (2 * ((c + e) ^ 2 + t ^ 2)) := by
  set G : ℝ → ℝ := fun p ↦ -((p + e) / (2 * ((p + e) ^ 2 + t ^ 2))) with hG
  have hd : ∀ p, HasDerivAt G (shearDensity (p + e) t) p := fun p ↦ by
    have h := ((hasDerivAt_shearPrimitive ht.ne' (p + e)).comp_add_const p e).neg
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun q ↦ ?_)
    · rw [shearDensity_comm, neg_neg]
    · simp only [hG, Pi.neg_apply, add_comm ((q + e) ^ 2)]
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h₁ : Tendsto (fun p : ℝ ↦ (p + e)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ e tendsto_id)
    refine squeeze_zero_norm' ?_ h₁
    filter_upwards [eventually_gt_atTop (-e)] with p hp
    have hp' : 0 < p + e := by linarith
    rw [hG, norm_neg, Real.norm_eq_abs, abs_div, abs_of_pos hp', abs_of_pos (by positivity),
      div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hp']
    nlinarith [sq_nonneg t, sq_nonneg (p + e)]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hd c).continuousAt.continuousWithinAt
    (fun p _ ↦ hd p) (integrable_shearDensity_add ht e).integrableOn hlim, hG]
  ring

/-- For `0 < t ≤ B`, the localized row mass `∫_0^∞ |Δ_B(p, t)| dp` is at most the full one: the
two kernels have the same mass and the positive part of `Δ_B` is the smaller one. -/
theorem lintegral_enorm_localShearDifference_le {B t : ℝ} (hB : 1 ≤ B) (ht : 0 < t)
    (htB : t ≤ B) :
    ∫⁻ p in Ioi 0, ‖localShearDifference B p t‖ₑ ≤ ∫⁻ p in Ioi 0, ‖shearDifference p t‖ₑ := by
  have hKp := integrable_shearDensity_add ht 1
  have hKm : Integrable fun p ↦ shearDensity (p - 1) t := by
    simpa only [sub_eq_add_neg] using integrable_shearDensity_add ht (-1)
  have hf : Integrable fun p ↦ shearDifference p t := hKp.sub hKm
  have hfB : Integrable fun p ↦ localShearDifference B p t := by
    refine (hKp.abs.add hKm.abs).mono' ((measurable_localShearDifference B).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ ?_)
    simp only [Real.norm_eq_abs, localShearDifference]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> split_ifs <;> simp
  -- the two rows have the same mass
  have hdiff : ∀ p ∈ Ioi (0 : ℝ), shearDifference p t - localShearDifference B p t =
      (Ioi (B - 1)).indicator (fun p ↦ shearDensity (p + 1) t) p -
        (Ioi (B + 1)).indicator (fun p ↦ shearDensity (p - 1) t) p := by
    intro p (hp0 : 0 < p)
    rcases le_or_gt (p + 1) B with h₁ | h₁
    · rw [localShearDifference_of_le (by rwa [abs_of_pos hp0]),
        indicator_of_notMem (notMem_Ioi.2 (by linarith)),
        indicator_of_notMem (notMem_Ioi.2 (by linarith))]
      ring
    rcases le_or_gt p (B + 1) with h₂ | h₂
    · rw [localShearDifference_of_lt hB h₁ h₂, indicator_of_mem (mem_Ioi.2 (by linarith)),
        indicator_of_notMem (notMem_Ioi.2 h₂), shearDifference]
      ring
    · rw [localShearDifference_of_gt h₂, indicator_of_mem (mem_Ioi.2 (by linarith)),
        indicator_of_mem (mem_Ioi.2 h₂), shearDifference]
      ring
  have hmass : ∫ p in Ioi 0, localShearDifference B p t = ∫ p in Ioi 0, shearDifference p t := by
    have hI {c : ℝ} (hc : 0 ≤ c) (g : ℝ → ℝ) :
        ∫ p in Ioi (0 : ℝ), (Ioi c).indicator g p = ∫ p in Ioi c, g p := by
      rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
        inter_eq_left.2 (Ioi_subset_Ioi hc)]
    have h₃ : ∫ p in Ioi (B + 1), shearDensity (p - 1) t =
        ∫ p in Ioi (B + 1), shearDensity (p + -1) t := by
      simp only [sub_eq_add_neg]
    have h0 : ∫ p in Ioi (0 : ℝ), (shearDifference p t - localShearDifference B p t) = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioi hdiff, integral_sub
        ((hKp.indicator measurableSet_Ioi).integrableOn)
        ((hKm.indicator measurableSet_Ioi).integrableOn), hI (by linarith), hI (by linarith), h₃,
        integral_Ioi_shearDensity_add ht, integral_Ioi_shearDensity_add ht]
      ring_nf
    rw [integral_sub hf.integrableOn hfB.integrableOn] at h0
    linarith
  -- the positive parts are ordered
  have hpos : ∀ p ∈ Ioi (0 : ℝ), max (localShearDifference B p t) 0 ≤
      max (shearDifference p t) 0 := by
    intro p (hp0 : 0 < p)
    rcases le_or_gt (p + 1) B with h₁ | h₁
    · rw [localShearDifference_of_le (by rwa [abs_of_pos hp0])]
    rcases le_or_gt p (B + 1) with h₂ | h₂
    · rw [localShearDifference_of_lt hB h₁ h₂]
      refine max_le_max ?_ le_rfl
      have : 0 ≤ shearDensity (p + 1) t := by
        rw [shearDensity_eq]
        refine div_nonneg ?_ (by positivity)
        nlinarith
      rw [shearDifference]
      linarith
    · rw [localShearDifference_of_gt h₂, max_self]
      exact le_max_right _ _
  have habs (x : ℝ) : ‖x‖ = 2 * max x 0 - x := by
    rcases le_total 0 x with h | h
    · rw [Real.norm_eq_abs, abs_of_nonneg h, max_eq_left h]; ring
    · rw [Real.norm_eq_abs, abs_of_nonpos h, max_eq_right h]; ring
  rw [← ofReal_integral_norm_eq_lintegral_enorm hfB.integrableOn,
    ← ofReal_integral_norm_eq_lintegral_enorm hf.integrableOn]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [habs]
  rw [integral_sub (hfB.pos_part.integrableOn.const_mul 2) hfB.integrableOn,
    integral_sub (hf.pos_part.integrableOn.const_mul 2) hf.integrableOn, integral_const_mul,
    integral_const_mul, hmass]
  have := setIntegral_mono_on hfB.pos_part.integrableOn hf.pos_part.integrableOn
    measurableSet_Ioi hpos
  linarith

/-- `S_out(B, h) ≤ 2 (2h)^{1/2} W(h)`. -/
theorem shearOuterCost_le_envelope {B h : ℝ} (hB : 4 ≤ B) (hh : 0 < h) :
    shearOuterCost B h ≤ ENNReal.ofReal (2 * (2 * h) ^ (1 / 2 : ℝ)) * shearOuterMass h := by
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (Ioc h B)) (f := fun p t ↦ ‖localShearDifference B p t‖ₑ)
    (measurable_localShearDifference B).enorm.aemeasurable
  rw [shearOuterCost, shearOuterMass, hswap, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_ofNat]
  gcongr _ * ?_
  calc ∫⁻ t in Ioc h B, ∫⁻ p in Ioi 0, ‖localShearDifference B p t‖ₑ
      ≤ ∫⁻ t in Ioc h B, ∫⁻ p in Ioi 0, ‖shearDifference p t‖ₑ :=
        setLIntegral_mono' measurableSet_Ioc fun t ht ↦
          lintegral_enorm_localShearDifference_le (by linarith) (hh.trans ht.1) ht.2
    _ ≤ _ := lintegral_mono_set Ioc_subset_Ioi_self

/-! ### The mass cost -/

/-- Translation of a lower integral over a half-line. -/
theorem lintegral_Ioi_add_const (b c : ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ p in Ioi (b + c), F p = ∫⁻ y in Ioi b, F (y + c) := by
  rw [← image_add_const_Ioi, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun x _ ↦ ((hasDerivAt_id' x).add_const c).hasDerivWithinAt) (add_left_injective c).injOn]
  simp

/-- `S̃_{1D}(B, A) ≤ X(A)`. -/
theorem shearMassCost_le_envelope {B A : ℝ} (hB : 4 ≤ B) (hA : 0 < A) :
    shearMassCost B A ≤ shearMassEnvelope A := by
  have hgle : ∀ p : ℝ, 0 ≤ p → A / ((p + 1) ^ 2 + A ^ 2) ≤ A / ((p - 1) ^ 2 + A ^ 2) :=
    fun p hp ↦ div_le_div_of_nonneg_left hA.le (by positivity) (by nlinarith)
  have hd₀ : Disjoint (Ioc 0 (B - 1)) (Ioi (B - 1)) := Ioc_disjoint_Ioi_same
  have hd₁ : Disjoint (Ioc (B - 1) (B + 1)) (Ioi (B + 1)) := Ioc_disjoint_Ioi_same
  have hs₀ : Ioi (0 : ℝ) = Ioc 0 (B - 1) ∪ Ioi (B - 1) := (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  have hs₁ : Ioi (B - 1) = Ioc (B - 1) (B + 1) ∪ Ioi (B + 1) :=
    (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  -- the masses beyond `B - 1`
  have ha : (∫⁻ p in Ioi (B - 1), ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) *
        (A / ((p - 1) ^ 2 + A ^ 2) - A / ((p + 1) ^ 2 + A ^ 2)))) +
      ∫⁻ p in Ioi (B - 1), ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * (A / ((p + 1) ^ 2 + A ^ 2))) =
      (∫⁻ p in Ioc (B - 1) (B + 1), ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) *
        (A / ((p - 1) ^ 2 + A ^ 2)))) +
      ∫⁻ p in Ioi (B + 1), ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) *
        (A / ((p - 1) ^ 2 + A ^ 2))) := by
    rw [← lintegral_add_left (by fun_prop), ← lintegral_union measurableSet_Ioi hd₁, ← hs₁]
    refine setLIntegral_congr_fun measurableSet_Ioi fun p hp ↦ ?_
    have hp0 : 0 < p := by simp only [mem_Ioi] at hp; linarith
    rw [← ENNReal.ofReal_add (mul_nonneg (by positivity) (sub_nonneg.2 (hgle p hp0.le)))
      (by positivity)]
    congr 1
    ring
  have hb : ∫⁻ p in Ioi (B - 1), ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) *
        (A / ((p + 1) ^ 2 + A ^ 2))) ≤
      ∫⁻ p in Ioi (B + 1), ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) *
        (A / ((p - 1) ^ 2 + A ^ 2))) := by
    rw [show B - 1 = B + -1 by ring, lintegral_Ioi_add_const, lintegral_Ioi_add_const]
    refine setLIntegral_mono' measurableSet_Ioi fun y hy ↦ ?_
    have hy : B < y := hy
    rw [show y + -1 + 1 = y by ring, show y + 1 - 1 = y by ring]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have hc : ∫⁻ p in Ioi (B + 1), ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) *
      (A / ((p - 1) ^ 2 + A ^ 2))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 2 * (4 * Real.sqrt 2 * A) /
      Real.sqrt (B + 1))) ?_
    rw [← lintegral_Ioi_div_mul_sqrt (by linarith) (by positivity)]
    refine setLIntegral_mono' measurableSet_Ioi fun p hp ↦ ENNReal.ofReal_le_ofReal ?_
    have hp : B + 1 < p := hp
    have hp0 : 0 < p := by linarith
    have hs := Real.sqrt_pos.2 hp0
    have hss := Real.mul_self_sqrt hp0.le
    rw [Real.mul_rpow (by norm_num) hp0.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have e : Real.sqrt 2 * Real.sqrt p * A * (p * Real.sqrt p) =
        Real.sqrt 2 * A * (p * (Real.sqrt p * Real.sqrt p)) := by ring
    rw [e, hss]
    have h4 : p * p ≤ 4 * ((p - 1) ^ 2 + A ^ 2) := by nlinarith
    have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ Real.sqrt 2 * A)
    linarith
  have hCX : ∫⁻ p in Ioc (B - 1) (B + 1), ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) *
        (A / ((p - 1) ^ 2 + A ^ 2))) ≤
      ∫⁻ p in Ioi (B - 1), ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) *
        (A / ((p - 1) ^ 2 + A ^ 2) - A / ((p + 1) ^ 2 + A ^ 2))) := by
    refine ENNReal.le_of_add_le_add_right hc ?_
    rw [← ha]
    gcongr
  -- the column masses
  have hc₀ : ∀ p ∈ Ioc 0 (B - 1), ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |shearMass B A p|) =
      ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) *
        (A / ((p - 1) ^ 2 + A ^ 2) - A / ((p + 1) ^ 2 + A ^ 2))) := by
    intro p hp
    have h₁ : |p + 1| ≤ B := by rw [abs_of_pos (by linarith [hp.1])]; linarith [hp.2]
    have h₂ : |p - 1| ≤ B := abs_le.2 ⟨by linarith [hp.1], by linarith [hp.2]⟩
    rw [shearMass, ite_eq_left h₁, ite_eq_left h₂,
      abs_of_nonpos (sub_nonpos.2 (hgle p hp.1.le)), neg_sub]
  have hc₁ : ∀ p ∈ Ioc (B - 1) (B + 1),
      ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |shearMass B A p|) =
      ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * (A / ((p - 1) ^ 2 + A ^ 2))) := by
    intro p hp
    have h₁ : ¬|p + 1| ≤ B := by rw [abs_of_pos (by linarith [hp.1])]; linarith [hp.1]
    have h₂ : |p - 1| ≤ B := abs_le.2 ⟨by linarith [hp.1], by linarith [hp.2]⟩
    rw [shearMass, ite_eq_right h₁, ite_eq_left h₂, zero_sub, abs_neg,
      abs_of_nonneg (by positivity)]
  have hc₂ : ∀ p ∈ Ioi (B + 1),
      ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |shearMass B A p|) = 0 := by
    intro p (hp : B + 1 < p)
    rw [shearMass_of_lt (by rwa [abs_of_pos (by linarith)]), abs_zero, mul_zero,
      ENNReal.ofReal_zero]
  rw [shearMassCost, shearMassEnvelope, hs₀, lintegral_union measurableSet_Ioi hd₀,
    lintegral_union measurableSet_Ioi hd₀, setLIntegral_congr_fun measurableSet_Ioc hc₀, hs₁,
    lintegral_union measurableSet_Ioi hd₁, setLIntegral_congr_fun measurableSet_Ioc hc₁,
    setLIntegral_congr_fun measurableSet_Ioi hc₂, lintegral_zero, add_zero, ← hs₁]
  gcongr

/-- **The mass envelope in closed form**: `X(A) = √2 π / (√(1 + A²) + A)^{1/2}` for `A > 0`. -/
theorem shearMassEnvelope_eq {A : ℝ} (hA : 0 < A) :
    shearMassEnvelope A =
      ENNReal.ofReal (Real.sqrt 2 * Real.pi / Real.sqrt (Real.sqrt (1 + A ^ 2) + A)) := by
  -- the primitive of `u ↦ u/(u² - cu + β) - u/(u² + cu + β)` for `c² + δ² = 4β`, `δ > 0`
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ → ℝ → ℝ → ℝ, ∀ c δ β u, H c δ β u =
      (Real.log (u ^ 2 - c * u + β) - Real.log (u ^ 2 + c * u + β)) / 2 +
        c / δ * (Real.arctan ((2 * u - c) / δ) + Real.arctan ((2 * u + c) / δ)) :=
    ⟨_, fun _ _ _ _ ↦ rfl⟩
  have hQ : ∀ c δ β : ℝ, 0 < δ → c ^ 2 + δ ^ 2 = 4 * β → ∀ u : ℝ,
      0 < u ^ 2 - c * u + β ∧ 0 < u ^ 2 + c * u + β := by
    intro c δ β hδ h u
    constructor <;> nlinarith [sq_nonneg (2 * u - c), sq_nonneg (2 * u + c), pow_pos hδ 2]
  have hHd : ∀ c δ β : ℝ, 0 < δ → c ^ 2 + δ ^ 2 = 4 * β → ∀ u : ℝ,
      HasDerivAt (H c δ β) (u / (u ^ 2 - c * u + β) - u / (u ^ 2 + c * u + β)) u := by
    intro c δ β hδ h u
    obtain ⟨h₁, h₂⟩ := hQ c δ β hδ h u
    rw [show H c δ β = fun u ↦ _ from funext (hH c δ β)]
    have d₁ : HasDerivAt (fun u : ℝ ↦ u ^ 2 - c * u + β) (2 * u - c) u := by
      simpa using ((hasDerivAt_pow 2 u).sub ((hasDerivAt_id' u).const_mul c)).add_const β
    have d₂ : HasDerivAt (fun u : ℝ ↦ u ^ 2 + c * u + β) (2 * u + c) u := by
      simpa using ((hasDerivAt_pow 2 u).add ((hasDerivAt_id' u).const_mul c)).add_const β
    have d₃ : HasDerivAt (fun u : ℝ ↦ (2 * u - c) / δ) (2 / δ) u := by
      simpa using (((hasDerivAt_id' u).const_mul 2).sub_const c).div_const δ
    have d₄ : HasDerivAt (fun u : ℝ ↦ (2 * u + c) / δ) (2 / δ) u := by
      simpa using (((hasDerivAt_id' u).const_mul 2).add_const c).div_const δ
    refine ((((d₁.log h₁.ne').sub (d₂.log h₂.ne')).div_const 2).add
      ((d₃.arctan.add d₄.arctan).const_mul (c / δ))).congr_deriv ?_
    have e₁ : 1 + ((2 * u - c) / δ) ^ 2 = 4 * (u ^ 2 - c * u + β) / δ ^ 2 := by
      field_simp
      linear_combination h
    have e₂ : 1 + ((2 * u + c) / δ) ^ 2 = 4 * (u ^ 2 + c * u + β) / δ ^ 2 := by
      field_simp
      linear_combination h
    rw [e₁, e₂]
    field_simp
    ring
  have hHlim : ∀ c δ β : ℝ, 0 < δ → c ^ 2 + δ ^ 2 = 4 * β →
      Tendsto (H c δ β) atTop (𝓝 (c / δ * Real.pi)) := by
    intro c δ β hδ h
    rw [show H c δ β = fun u ↦ _ from funext (hH c δ β)]
    have hi : Tendsto (fun u : ℝ ↦ u⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hn : Tendsto (fun u : ℝ ↦ 1 - c * u⁻¹ + β * u⁻¹ ^ 2) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub (hi.const_mul c)).add ((hi.pow 2).const_mul β)
    have hd : Tendsto (fun u : ℝ ↦ 1 + c * u⁻¹ + β * u⁻¹ ^ 2) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.add (hi.const_mul c)).add ((hi.pow 2).const_mul β)
    have hlog : Tendsto (fun u : ℝ ↦ Real.log (u ^ 2 - c * u + β) -
        Real.log (u ^ 2 + c * u + β)) atTop (𝓝 0) := by
      have hq := hn.div hd one_ne_zero
      rw [div_one] at hq
      have := (Real.continuousAt_log one_ne_zero).tendsto.comp hq
      rw [Real.log_one] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with u hu
      obtain ⟨h₁, h₂⟩ := hQ c δ β hδ h u
      rw [Function.comp_apply, Pi.div_apply, ← Real.log_div h₁.ne' h₂.ne']
      congr 1
      field_simp
    have hlin : ∀ e : ℝ, Tendsto (fun u : ℝ ↦ (2 * u + e) / δ) atTop atTop := fun e ↦
      (tendsto_atTop_add_const_right _ e (tendsto_id.const_mul_atTop two_pos)).atTop_div_const hδ
    have hlin' : Tendsto (fun u : ℝ ↦ (2 * u - c) / δ) atTop atTop := by
      simpa only [sub_eq_add_neg] using hlin (-c)
    have harc := Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
    have := (hlog.div_const 2).add (((harc.comp hlin').add (harc.comp (hlin c))).const_mul (c / δ))
    rw [show c / δ * Real.pi = 0 / 2 + c / δ * (Real.pi / 2 + Real.pi / 2) by ring]
    exact this
  have hH0 : ∀ c δ β : ℝ, H c δ β 0 = 0 := by
    intro c δ β
    rw [hH]
    simp [neg_div, Real.arctan_neg]
  -- the constants `β = √(1 + A²)`, `c = √(2β + 2)`, `d = √(2β - 2)`
  set β := Real.sqrt (1 + A ^ 2) with hβdef
  have hβ2 : β ^ 2 = 1 + A ^ 2 := Real.sq_sqrt (by positivity)
  have hβ1 : 1 < β := by
    rw [hβdef, Real.lt_sqrt zero_le_one]
    nlinarith
  set c := Real.sqrt (2 * β + 2) with hcdef
  set d := Real.sqrt (2 * β - 2) with hddef
  have hc2 : c ^ 2 = 2 * β + 2 := Real.sq_sqrt (by linarith)
  have hd2 : d ^ 2 = 2 * β - 2 := Real.sq_sqrt (by linarith)
  have hc0 : 0 < c := Real.sqrt_pos.2 (by linarith)
  have hd0 : 0 < d := Real.sqrt_pos.2 (by linarith)
  have hcd : c * d = 2 * A := by
    rw [hcdef, hddef, ← Real.sqrt_mul (by linarith),
      show (2 * β + 2) * (2 * β - 2) = (2 * A) ^ 2 by linear_combination 4 * hβ2,
      Real.sqrt_sq (by linarith)]
  have h₁ : c ^ 2 + d ^ 2 = 4 * β := by linarith
  have h₂ : d ^ 2 + c ^ 2 = 4 * β := by linarith
  -- the primitive in `u = √p`
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ u, F u =
      2 * Real.sqrt 2 * A * (1 / (2 * c) * H c d β u - 1 / (2 * d) * H d c β u) :=
    ⟨_, fun _ ↦ rfl⟩
  have hFd : ∀ u, HasDerivAt F (2 * Real.sqrt 2 * A *
      (1 / (2 * c) * (u / (u ^ 2 - c * u + β) - u / (u ^ 2 + c * u + β)) -
        1 / (2 * d) * (u / (u ^ 2 - d * u + β) - u / (u ^ 2 + d * u + β)))) u := by
    intro u
    rw [show F = fun u ↦ _ from funext hF]
    exact (((hHd c d β hd0 h₁ u).const_mul _).sub ((hHd d c β hc0 h₂ u).const_mul _)).const_mul _
  have hFlim : Tendsto F atTop (𝓝 (2 * Real.sqrt 2 * A *
      (1 / (2 * c) * (c / d * Real.pi) - 1 / (2 * d) * (d / c * Real.pi)))) := by
    rw [show F = fun u ↦ _ from funext hF]
    exact (((hHlim c d β hd0 h₁).const_mul _).sub ((hHlim d c β hc0 h₂).const_mul _)).const_mul _
  have hF0 : F 0 = 0 := by
    rw [hF, hH0, hH0]
    ring
  -- the primitive in `p`
  have hGd : ∀ p ∈ Ioi (0 : ℝ), HasDerivAt (fun p ↦ F (Real.sqrt p))
      ((2 * p) ^ (1 / 2 : ℝ) * (A / ((p - 1) ^ 2 + A ^ 2) - A / ((p + 1) ^ 2 + A ^ 2))) p := by
    intro p hp
    have hp0 : 0 < p := hp
    refine ((hFd (Real.sqrt p)).comp p (Real.hasDerivAt_sqrt hp0.ne')).congr_deriv ?_
    have hss : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
    have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 hp0
    rw [Real.mul_rpow (by norm_num) hp0.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    obtain ⟨q₁, q₂⟩ := hQ c d β hd0 h₁ (Real.sqrt p)
    obtain ⟨q₃, q₄⟩ := hQ d c β hc0 h₂ (Real.sqrt p)
    have e₁ : (Real.sqrt p ^ 2 - c * Real.sqrt p + β) * (Real.sqrt p ^ 2 + c * Real.sqrt p + β) =
        (p - 1) ^ 2 + A ^ 2 := by
      linear_combination (-Real.sqrt p ^ 2) * hc2 + hβ2 + (Real.sqrt p ^ 2 + p - 2) * hss
    have e₂ : (Real.sqrt p ^ 2 - d * Real.sqrt p + β) * (Real.sqrt p ^ 2 + d * Real.sqrt p + β) =
        (p + 1) ^ 2 + A ^ 2 := by
      linear_combination (-Real.sqrt p ^ 2) * hd2 + hβ2 + (Real.sqrt p ^ 2 + p + 2) * hss
    have k₁ : Real.sqrt p / (Real.sqrt p ^ 2 - c * Real.sqrt p + β) -
        Real.sqrt p / (Real.sqrt p ^ 2 + c * Real.sqrt p + β) =
        2 * c * Real.sqrt p ^ 2 / ((p - 1) ^ 2 + A ^ 2) := by
      rw [div_sub_div _ _ q₁.ne' q₂.ne', e₁]
      congr 1
      ring
    have k₂ : Real.sqrt p / (Real.sqrt p ^ 2 - d * Real.sqrt p + β) -
        Real.sqrt p / (Real.sqrt p ^ 2 + d * Real.sqrt p + β) =
        2 * d * Real.sqrt p ^ 2 / ((p + 1) ^ 2 + A ^ 2) := by
      rw [div_sub_div _ _ q₃.ne' q₄.ne', e₂]
      congr 1
      ring
    have hP₁ : (p - 1) ^ 2 + A ^ 2 ≠ 0 := by positivity
    have hP₂ : (p + 1) ^ 2 + A ^ 2 ≠ 0 := by positivity
    rw [k₁, k₂]
    field_simp
  have hGpos : ∀ p ∈ Ioi (0 : ℝ), 0 ≤ (2 * p) ^ (1 / 2 : ℝ) *
      (A / ((p - 1) ^ 2 + A ^ 2) - A / ((p + 1) ^ 2 + A ^ 2)) := fun p hp ↦ by
    have hp0 : 0 < p := hp
    exact mul_nonneg (by positivity)
      (sub_nonneg.2 (div_le_div_of_nonneg_left hA.le (by positivity) (by nlinarith)))
  have hGc : ContinuousWithinAt (fun p ↦ F (Real.sqrt p)) (Ici 0) 0 :=
    ((continuous_iff_continuousAt.2 fun u ↦ (hFd u).continuousAt).comp
      Real.continuous_sqrt).continuousWithinAt
  have hGlim := hFlim.comp Real.tendsto_sqrt_atTop
  rw [shearMassEnvelope, ← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioi_deriv_of_nonneg hGc hGd hGpos hGlim),
    integral_Ioi_of_hasDerivAt_of_nonneg hGc hGd hGpos hGlim]
  · congr 1
    simp only [Real.sqrt_zero, hF0, sub_zero]
    have hr0 : 0 < Real.sqrt (β + A) := Real.sqrt_pos.2 (by linarith)
    have hr2 : Real.sqrt (β + A) ^ 2 = β + A := Real.sq_sqrt (by linarith)
    have hcd0 : 0 < c - d := by nlinarith
    have hsq : ((c - d) * Real.sqrt (β + A)) ^ 2 = 2 ^ 2 := by
      rw [mul_pow, hr2]
      linear_combination (β + A) * h₁ - 2 * (β + A) * hcd + 4 * hβ2
    have hr : (c - d) * Real.sqrt (β + A) = 2 := by nlinarith [mul_pos hcd0 hr0]
    rw [eq_div_iff hr0.ne']
    field_simp
    linear_combination A * hr - hcd
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp using hGpos p hp

/-! ### The constant -/

/-- The envelope `X(A) + τ (U(A) + 2 (2A)^{1/2} W(A))` at the height `A`. -/
def shearHolderEnvelope (τ A : ℝ) : ℝ≥0∞ :=
  shearMassEnvelope A + ENNReal.ofReal τ *
    (shearUpperEnvelope A + ENNReal.ofReal (2 * (2 * A) ^ (1 / 2 : ℝ)) * shearOuterMass A)

/-- **The envelope bound of `C₂(τ)`**: the constant of Chen and Hou, Part I, Lemma 3.4 for `u_y`
is at most `sup_{A > 0} (X(A) + τ (U(A) + 2 (2A)^{1/2} W(A))) / √2`. -/
theorem shearConstant_le_iSup_envelope {τ : ℝ} :
    shearConstant τ ≤ ⨆ (A : ℝ) (_ : 0 < A), shearHolderEnvelope τ A /
      ENNReal.ofReal (Real.sqrt 2) := by
  refine iSup₂_le fun h hh ↦ iSup₂_le fun B hB ↦ ?_
  have hA : 0 < min h B := lt_min hh (by linarith)
  have hout : shearOuterCost B h ≤
      ENNReal.ofReal (2 * (2 * min h B) ^ (1 / 2 : ℝ)) * shearOuterMass (min h B) := by
    rcases lt_or_ge h B with hhB | hhB
    · rw [min_eq_left hhB.le]
      exact shearOuterCost_le_envelope hB hh
    · have h0 : shearOuterCost B h = 0 := by
        rw [shearOuterCost, Ioc_eq_empty (not_lt.2 hhB)]
        simp
      rw [h0]
      exact zero_le
  refine le_iSup₂_of_le (min h B) hA ?_
  unfold shearHolderEnvelope
  gcongr
  · exact shearMassCost_le_envelope hB hA
  · exact shearUpperCost_le_envelope hB (min_le_right _ _)

end IncompressibleFlow.SharpHolder
