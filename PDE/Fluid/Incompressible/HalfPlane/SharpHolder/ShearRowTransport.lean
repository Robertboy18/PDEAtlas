/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearRowMap
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearTransport

/-!
# Horizontal transport on the rows of the vertical Hölder estimate of `u_y` and `v_x`

Chen and Hou, Part I, Appendix B.2: after rotating and rescaling, the nonlocal part of the
difference of the unlocalized `u_y` (or `v_x`) at two points on a vertical line reduces to
`∫ Δ(p, q) η(p, q) dp dq` with `Δ(p, q) = K₂(p + 1, q) - K₂(p - 1, q)` and the two points at
`(± 1, 0)`. On a row `q > 0` and `|p| ≤ m` the kernel `Δ(·, q)` is odd, and on `p ≥ 0`:

* below `h_c^-(q)` it is nonpositive (zero at `p = 0`) and above it, up to
  `T_y(0, q) = (1 - 3q²)^{1/2}`, nonnegative, with zero mass on `[0, T_y(0, q)]`;
* between `1` and `h_c^+(q)` it is nonnegative and above `h_c^+(q)` nonpositive, with zero mass on
  `[T_y(m, q), m]` when `h_c^+(q) < m`.

The two balanced intervals are transported horizontally by the map `T_y` of (B.67)
(`horizontalShearMap`), and the rest is compared with the row at `-p`. The resulting row estimate
`abs_integral_shearDifference_mul_le_row` is the per-row form of Part I, (B.46)-(B.50) and
(B.51)-(B.53).

## Main results

* `abs_setIntegral_Icc_mul_le_right`, `abs_setIntegral_Icc_mul_le_left`: the transport lemma
  (Part I, Lemma 3.6) on a balanced interval for a kernel with an explicit primitive, with the
  cost on the right or on the left side of the sign change.
* `shearDifference_nonpos_of_lt_lowerShearThreshold`,
  `shearDifference_nonneg_of_lowerShearThreshold_lt`,
  `shearDifference_nonpos_of_upperShearThreshold_lt`: the signs (B.46) of `Δ` along rows.
* `shearInnerRowCost`, `shearMidRowCost`: the row costs.
* `abs_integral_shearDifference_mul_le_row`: the row estimate.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Lemma 3.6, p. 29, Appendix B.2,
  pp. 136-141, and (B.62), (B.67), pp. 141-142.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter PDE.Analysis.Rearrangement
open scoped ENNReal NNReal Topology

namespace IncompressibleFlow.SharpHolder

section Balanced

variable {k Ψ T G : ℝ → ℝ} {s c t : ℝ} {C : ℝ≥0}

/-- **Transport on a balanced interval, cost on the right.** Let `k` be continuous on `[s, t]`
with primitive `Ψ`, `Ψ(s) = Ψ(t)`, nonpositive on `[s, c)` and nonnegative on `(c, t]`, and let
`T` be measurable, mapping `(c, t]` into `[s, c)` with `Ψ(T y) = Ψ(y)`. For `G` `1/2`-Hölder with
constant `C` on `[s, t]`,
`|∫_s^t k G| ≤ C ∫_c^t |k(y)| |y - T y|^{1/2} dy` (Chen and Hou, Part I, Lemma 3.6). -/
theorem abs_setIntegral_Icc_mul_le_right (hsc : s ≤ c) (hct : c ≤ t)
    (hk : ContinuousOn k (Icc s t)) (hΨ : ∀ x ∈ Icc s t, HasDerivAt Ψ (k x) x)
    (hbal : Ψ s = Ψ t) (hneg : ∀ x ∈ Ico s c, k x ≤ 0) (hpos : ∀ x ∈ Ioc c t, 0 ≤ k x)
    (hTm : Measurable T) (hT : ∀ y ∈ Ioc c t, T y ∈ Ico s c)
    (hmass : ∀ y ∈ Ioc c t, Ψ (T y) = Ψ y) (hG : HolderOnWith C (1 / 2) G (Icc s t)) :
    ENNReal.ofReal |∫ x in Icc s t, k x * G x| ≤
      C * ∫⁻ y in Ioc c t, ‖k y‖ₑ * ENNReal.ofReal (|y - T y| ^ (1 / 2 : ℝ)) := by
  set S : Set ℝ := Icc s t with hS
  set κ : ℝ → ℝ := S.indicator k with hκ
  have hκi : Integrable κ := (integrable_indicator_iff measurableSet_Icc).2 hk.integrableOn_Icc
  have hzero : ∫ x, κ x = 0 := by
    rw [hκ, integral_indicator measurableSet_Icc,
      setIntegral_Icc_eq_sub_of_hasDerivAt (hsc.trans hct) hk hΨ, hbal, sub_self]
  have hκneg : ∀ᵐ x, x < c → κ x ≤ 0 :=
    Eventually.of_forall fun x hx ↦ indicator_apply_nonpos fun h ↦ hneg x ⟨h.1, hx⟩
  have hκpos : ∀ᵐ x, c < x → 0 ≤ κ x :=
    Eventually.of_forall fun x hx ↦ indicator_apply_nonneg fun h ↦ hpos x ⟨hx, h.2⟩
  have hint : Integrable fun x ↦ κ x * |x - c| ^ ((1 / 2 : ℝ≥0) : ℝ) := by
    rw [show (fun x ↦ κ x * _) = S.indicator fun x ↦ k x * |x - c| ^ ((1 / 2 : ℝ≥0) : ℝ) by
      ext x; simp only [hκ, indicator_mul_left], integrable_indicator_iff measurableSet_Icc]
    exact (hk.mul (Continuous.continuousOn (by fun_prop (disch := positivity)))).integrableOn_Icc
  have hTeq : ∀ᵐ y ∂volume.restrict (Ioi c), κ y ≠ 0 → ∫ x in T y..y, κ x = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : c < y) hκy
    have hyS : y ∈ S := mem_of_indicator_ne_zero hκy
    have hTy := hT y ⟨hy, hyS.2⟩
    have hTyy : T y ≤ y := (hTy.2.trans hy).le
    have hsub : Icc (T y) y ⊆ S := Icc_subset_Icc hTy.1 hyS.2
    rw [intervalIntegral.integral_of_le hTyy, ← integral_Icc_eq_integral_Ioc,
      setIntegral_congr_fun measurableSet_Icc (fun x hx ↦ by
        rw [hκ, indicator_of_mem (hsub hx)] : EqOn κ k (Icc (T y) y)),
      setIntegral_Icc_eq_sub_of_hasDerivAt hTyy (hk.mono hsub) (fun x hx ↦ hΨ x (hsub hx)),
      hmass y ⟨hy, hyS.2⟩, sub_self]
  have hmain := abs_integral_mul_le_of_integral_eq_zero hκi hκneg hκpos hzero hint
    hTm.aemeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : c < y) hκy using
        (hT y ⟨hy, (mem_of_indicator_ne_zero hκy).2⟩).2)
    hTeq (by norm_num) measurableSet_Icc
    (Eventually.of_forall fun x hx ↦ mem_of_indicator_ne_zero hx) ⟨hsc, hct⟩ hG
  have hlhs : ∫ x, κ x * G x = ∫ x in S, k x * G x := by
    rw [← integral_indicator measurableSet_Icc]
    congr 1 with x
    simp only [hκ, hS, indicator_mul_left]
  have hrhs : ∫ y in Ioi c, |κ y| * |y - T y| ^ ((1 / 2 : ℝ≥0) : ℝ) =
      ∫ y in Ioc c t, |k y| * |y - T y| ^ (1 / 2 : ℝ) := by
    rw [show Ioc c t = Ioi c ∩ S from Subset.antisymm (fun y hy ↦ ⟨hy.1, hsc.trans hy.1.le,
      hy.2⟩) fun y hy ↦ ⟨hy.1, hy.2.2⟩, ← setIntegral_indicator measurableSet_Icc]
    congr 1 with y
    simp only [hκ, hS, indicator_mul_left, ← Real.norm_eq_abs, norm_indicator_eq_indicator_norm]
    norm_num
  rw [hlhs, hrhs] at hmain
  have hnn : 0 ≤ ∫ y in Ioc c t, |k y| * |y - T y| ^ (1 / 2 : ℝ) :=
    setIntegral_nonneg measurableSet_Ioc fun y _ ↦ by positivity
  calc ENNReal.ofReal |∫ x in S, k x * G x|
      ≤ ENNReal.ofReal (C * ∫ y in Ioc c t, |k y| * |y - T y| ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_le_ofReal hmain
    _ = C * ENNReal.ofReal (∫ y in Ioc c t, |k y| * |y - T y| ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    _ ≤ C * ∫⁻ y in Ioc c t, ‖k y‖ₑ * ENNReal.ofReal (|y - T y| ^ (1 / 2 : ℝ)) := by
        gcongr
        rw [← abs_of_nonneg hnn, ← Real.enorm_eq_ofReal_abs]
        refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
        refine setLIntegral_congr_fun measurableSet_Ioc fun y _ ↦ ?_
        rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ |y - T y| ^ (1 / 2 : ℝ)),
          Real.enorm_eq_ofReal_abs]

/-- **Transport on a balanced interval, cost on the left.** As
`abs_setIntegral_Icc_mul_le_right`, with `T` mapping `[s, c)` into `(c, t]`:
`|∫_s^t k G| ≤ C ∫_s^c |k(x)| |T x - x|^{1/2} dx`. The proof reflects `x ↦ -x`. -/
theorem abs_setIntegral_Icc_mul_le_left (hsc : s ≤ c) (hct : c ≤ t)
    (hk : ContinuousOn k (Icc s t)) (hΨ : ∀ x ∈ Icc s t, HasDerivAt Ψ (k x) x)
    (hbal : Ψ s = Ψ t) (hneg : ∀ x ∈ Ico s c, k x ≤ 0) (hpos : ∀ x ∈ Ioc c t, 0 ≤ k x)
    (hTm : Measurable T) (hT : ∀ x ∈ Ico s c, T x ∈ Ioc c t)
    (hmass : ∀ x ∈ Ico s c, Ψ (T x) = Ψ x) (hG : HolderOnWith C (1 / 2) G (Icc s t)) :
    ENNReal.ofReal |∫ x in Icc s t, k x * G x| ≤
      C * ∫⁻ x in Ico s c, ‖k x‖ₑ * ENNReal.ofReal (|T x - x| ^ (1 / 2 : ℝ)) := by
  have hneg' : ∀ x, x ∈ Icc (-t) (-s) ↔ -x ∈ Icc s t := fun x ↦ by
    simp only [mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have h := abs_setIntegral_Icc_mul_le_right (k := fun x ↦ -k (-x)) (Ψ := fun x ↦ Ψ (-x))
    (T := fun y ↦ -T (-y)) (G := fun x ↦ G (-x)) (s := -t) (c := -c) (t := -s) (C := C)
    (by linarith) (by linarith)
    ((hk.comp continuous_neg.continuousOn fun x hx ↦ (hneg' x).1 hx).neg)
    (fun x hx ↦ ((hΨ (-x) ((hneg' x).1 hx)).comp x (hasDerivAt_neg x)).congr_deriv (by ring))
    (by simp only [neg_neg]; exact hbal.symm)
    (fun x hx ↦ neg_nonpos.2 (hpos (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩))
    (fun x hx ↦ neg_nonneg.2 (hneg (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩))
    (measurable_neg.comp (hTm.comp measurable_neg))
    (fun y hy ↦ by
      have := hT (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
      exact ⟨by linarith [this.2], by linarith [this.1]⟩)
    (fun y hy ↦ by simpa only [neg_neg] using hmass (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩)
    (fun x hx y hy ↦ by
      simpa only [edist_neg_neg] using hG (-x) ((hneg' x).1 hx) (-y) ((hneg' y).1 hy))
  have hl : ∫ x in Icc (-t) (-s), -k (-x) * G (-x) = -∫ x in Icc s t, k x * G x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hsc.trans hct),
      ← intervalIntegral.integral_neg]
    have := intervalIntegral.integral_comp_neg (a := -t) (b := -s) (fun x ↦ -(k x * G x))
    simp only [neg_neg] at this
    rw [show (fun x ↦ -k (-x) * G (-x)) = fun x ↦ -(k (-x) * G (-x)) by ext; ring, this]
  have hr : ∫⁻ y in Ioc (-c) (-s), ‖-k (-y)‖ₑ * ENNReal.ofReal (|y - -T (-y)| ^ (1 / 2 : ℝ)) =
      ∫⁻ x in Ico s c, ‖k x‖ₑ * ENNReal.ofReal (|T x - x| ^ (1 / 2 : ℝ)) := by
    have hpre : (fun x : ℝ ↦ -x) ⁻¹' Ico s c = Ioc (-c) (-s) := by
      ext x
      simp only [mem_preimage, mem_Ico, mem_Ioc]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
    conv_rhs => rw [← hmp.setLIntegral_comp_preimage_emb (Homeomorph.neg ℝ).measurableEmbedding]
    rw [← hpre]
    refine setLIntegral_congr_fun ((measurableSet_Ico).preimage measurable_neg) fun y _ ↦ ?_
    rw [enorm_neg, show y - -T (-y) = T (-y) - -y by ring]
  rwa [hl, abs_neg, hr] at h

end Balanced

/-! ### Signs of `Δ` along rows -/

/-- `u₋ ≤ h_c^-(q)²` and `h_c^+(q)² = u₊` for `q ≥ 0`, `u± = q² + 1 ± 2 q (q² + 1)^{1/2}`. -/
private theorem threshold_sq {q : ℝ} (hq : 0 ≤ q) :
    q ^ 2 + 1 - 2 * q * Real.sqrt (q ^ 2 + 1) ≤ lowerShearThreshold q ^ 2 ∧
      upperShearThreshold q ^ 2 = q ^ 2 + 1 + 2 * q * Real.sqrt (q ^ 2 + 1) := by
  refine ⟨?_, upperShearThreshold_sq hq⟩
  rw [lowerShearThreshold]
  rcases le_or_gt 0 (q ^ 2 + 1 - 2 * q * Real.sqrt (q ^ 2 + 1)) with h | h
  · rw [Real.sq_sqrt h]
  · rw [Real.sqrt_eq_zero_of_nonpos h.le]
    linarith

/-- `Δ = -2 p Q / (((p + 1)² + q²)² ((p - 1)² + q²)²)` with `Q = (p² - u₊)(p² - u₋)` on a row
`q > 0`. -/
private theorem shearDifference_eq_factor {p q : ℝ} (hq : 0 < q) :
    shearDifference p q = -2 * p * ((p ^ 2 - (q ^ 2 + 1 + 2 * q * Real.sqrt (q ^ 2 + 1))) *
      (p ^ 2 - (q ^ 2 + 1 - 2 * q * Real.sqrt (q ^ 2 + 1)))) /
      (((p + 1) ^ 2 + q ^ 2) ^ 2 * ((p - 1) ^ 2 + q ^ 2) ^ 2) := by
  rw [shearDifference_eq (by positivity) (by positivity), shearQuartic_eq_upper_lower]

/-- On a row `q > 0`, `Δ(p, q) ≤ 0` for `0 ≤ p < h_c^-(q)` (Chen and Hou, Part I, (B.46)). -/
theorem shearDifference_nonpos_of_lt_lowerShearThreshold {p q : ℝ} (hq : 0 < q) (hp : 0 ≤ p)
    (hlt : p < lowerShearThreshold q) : shearDifference p q ≤ 0 := by
  have hs := Real.sqrt_nonneg (q ^ 2 + 1)
  have h1 : p ^ 2 < q ^ 2 + 1 - 2 * q * Real.sqrt (q ^ 2 + 1) :=
    (Real.lt_sqrt hp).1 hlt
  have hQ : 0 < (p ^ 2 - (q ^ 2 + 1 + 2 * q * Real.sqrt (q ^ 2 + 1))) *
      (p ^ 2 - (q ^ 2 + 1 - 2 * q * Real.sqrt (q ^ 2 + 1))) :=
    mul_pos_of_neg_of_neg (by nlinarith) (by linarith)
  rw [shearDifference_eq_factor hq]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)

/-- On a row `q > 0`, `Δ(p, q) ≥ 0` for `h_c^-(q) < p < h_c^+(q)` (Chen and Hou, Part I,
(B.46)). -/
theorem shearDifference_nonneg_of_lowerShearThreshold_lt {p q : ℝ} (hq : 0 < q)
    (h₁ : lowerShearThreshold q < p) (h₂ : p < upperShearThreshold q) :
    0 ≤ shearDifference p q := by
  have hs := Real.sqrt_nonneg (q ^ 2 + 1)
  have hp : 0 < p := (Real.sqrt_nonneg _).trans_lt h₁
  obtain ⟨hl, hu⟩ := threshold_sq hq.le
  have hl' : q ^ 2 + 1 - 2 * q * Real.sqrt (q ^ 2 + 1) < p ^ 2 :=
    hl.trans_lt (pow_lt_pow_left₀ h₁ (Real.sqrt_nonneg _) two_ne_zero)
  have hu' : p ^ 2 < q ^ 2 + 1 + 2 * q * Real.sqrt (q ^ 2 + 1) := by
    rw [← hu]
    exact pow_lt_pow_left₀ h₂ hp.le two_ne_zero
  have hQ : (p ^ 2 - (q ^ 2 + 1 + 2 * q * Real.sqrt (q ^ 2 + 1))) *
      (p ^ 2 - (q ^ 2 + 1 - 2 * q * Real.sqrt (q ^ 2 + 1))) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  rw [shearDifference_eq_factor hq]
  exact div_nonneg (by nlinarith) (by positivity)

/-- On a row `q > 0`, `Δ(p, q) ≤ 0` for `p > h_c^+(q)` (Chen and Hou, Part I, (B.46)). -/
theorem shearDifference_nonpos_of_upperShearThreshold_lt {p q : ℝ} (hq : 0 < q)
    (h : upperShearThreshold q < p) : shearDifference p q ≤ 0 := by
  have hs := Real.sqrt_nonneg (q ^ 2 + 1)
  have hp : 0 < p := (Real.sqrt_nonneg _).trans_lt h
  obtain ⟨-, hu⟩ := threshold_sq hq.le
  have hu' : q ^ 2 + 1 + 2 * q * Real.sqrt (q ^ 2 + 1) < p ^ 2 := by
    rw [← hu]
    exact pow_lt_pow_left₀ h (Real.sqrt_nonneg _) two_ne_zero
  have hQ : 0 < (p ^ 2 - (q ^ 2 + 1 + 2 * q * Real.sqrt (q ^ 2 + 1))) *
      (p ^ 2 - (q ^ 2 + 1 - 2 * q * Real.sqrt (q ^ 2 + 1))) :=
    mul_pos (by linarith) (by nlinarith [mul_nonneg hq.le hs])
  rw [shearDifference_eq_factor hq]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)

/-! ### The row maps -/

/-- `T_y(0, q) = (1 - 3q²)^{1/2}`. -/
theorem horizontalShearMap_zero_left (q : ℝ) :
    horizontalShearMap 0 q = Real.sqrt (1 - 3 * q ^ 2) := by
  rw [horizontalShearMap]
  congr 1
  have : (0 : ℝ) ^ 2 - q ^ 2 - 1 ≠ 0 := by nlinarith [sq_nonneg q]
  field_simp
  ring

/-- `h_c^-(q) > 0` for `3q² < 1`. -/
theorem lowerShearThreshold_pos {q : ℝ} (hq : 0 ≤ q) (h3 : 3 * q ^ 2 < 1) :
    0 < lowerShearThreshold q := by
  refine Real.sqrt_pos.2 ?_
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ q ^ 2 + 1 by positivity)
  have h2 : 2 * q < Real.sqrt (q ^ 2 + 1) := by
    rw [Real.lt_sqrt (by linarith)]
    linarith
  nlinarith [Real.sqrt_nonneg (q ^ 2 + 1)]

/-- `h_c^-(q) ≤ 1` for `q ≥ 0`. -/
theorem lowerShearThreshold_le_one {q : ℝ} (hq : 0 ≤ q) : lowerShearThreshold q ≤ 1 := by
  rw [lowerShearThreshold, Real.sqrt_le_one]
  have : q ≤ Real.sqrt (q ^ 2 + 1) := Real.le_sqrt_of_sq_le (by linarith)
  nlinarith

/-- `h_c^+(q) ≥ 1` for `q ≥ 0`. -/
theorem one_le_upperShearThreshold {q : ℝ} (hq : 0 ≤ q) : 1 ≤ upperShearThreshold q := by
  rw [upperShearThreshold, Real.one_le_sqrt]
  nlinarith [Real.sqrt_nonneg (q ^ 2 + 1), sq_nonneg q]

/-- On `D₁` the radicand of (B.67) is nonnegative and `p² - q² - 1 < 0`. -/
private theorem lower_radicand {p q : ℝ} (hq : 0 < q) (h3 : 3 * q ^ 2 < 1) (hp : 0 ≤ p)
    (hlt : p < lowerShearThreshold q) :
    p ^ 2 - q ^ 2 - 1 < 0 ∧
      0 ≤ (p ^ 2 + 2 * q ^ 2 + p ^ 2 * q ^ 2 + 3 * q ^ 4 - 1) / (p ^ 2 - q ^ 2 - 1) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ q ^ 2 + 1 by positivity)
  have hs0 := Real.sqrt_nonneg (q ^ 2 + 1)
  have h1 : p ^ 2 < q ^ 2 + 1 - 2 * q * Real.sqrt (q ^ 2 + 1) := (Real.lt_sqrt hp).1 hlt
  have h2 : 2 * q ≤ Real.sqrt (q ^ 2 + 1) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hd : p ^ 2 - q ^ 2 - 1 < 0 := by nlinarith
  refine ⟨hd, ?_⟩
  rw [horizontalShearMap_radicand]
  exact div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by nlinarith))
    hd.le

/-- On `D₂` the radicand of (B.67) is nonnegative and `p² - q² - 1 > 0`. -/
private theorem upper_radicand {p q : ℝ} (hq : 0 < q) (hlt : upperShearThreshold q < p) :
    0 < p ^ 2 - q ^ 2 - 1 ∧
      0 ≤ (p ^ 2 + 2 * q ^ 2 + p ^ 2 * q ^ 2 + 3 * q ^ 4 - 1) / (p ^ 2 - q ^ 2 - 1) := by
  have hs0 := Real.sqrt_nonneg (q ^ 2 + 1)
  obtain ⟨-, hu⟩ := threshold_sq hq.le
  have h0 := Real.sqrt_nonneg (q ^ 2 + 1 + 2 * q * Real.sqrt (q ^ 2 + 1))
  have hu' : q ^ 2 + 1 + 2 * q * Real.sqrt (q ^ 2 + 1) < p ^ 2 := by
    rw [← hu]
    exact pow_lt_pow_left₀ hlt h0 two_ne_zero
  have hd : 0 < p ^ 2 - q ^ 2 - 1 := by nlinarith [mul_nonneg hq.le hs0]
  refine ⟨hd, ?_⟩
  rw [horizontalShearMap_radicand]
  exact div_nonneg (mul_nonneg (by positivity) (by nlinarith [mul_nonneg hq.le hs0])) hd.le

/-- The row map is measurable in `p`. -/
theorem measurable_horizontalShearMap_left (q : ℝ) :
    Measurable fun p ↦ horizontalShearMap p q := by
  unfold horizontalShearMap
  fun_prop

/-! ### The row estimate -/

/-- The right end `T_y(m, q)` of the remainder of a row in the middle region, `m` itself when
`h_c^+(q) ≥ m` (then no part of the row is transported). -/
def shearMidEdge (m q : ℝ) : ℝ :=
  if upperShearThreshold q < m then horizontalShearMap m q else m

/-- The cost of a row `q > 0` in the inner region `|p| ≤ 1` (Chen and Hou, Part I, (B.46)-(B.50)):
`2 ∫_0^{h_c^-(q)} |Δ(p, q)| |p - T_y(p, q)|^{1/2} dp + ∫_{T_y(0, q)}^{1} |Δ(p, q)| (2p)^{1/2} dp`.
For `3q² ≥ 1`, `h_c^-(q) = T_y(0, q) = 0`: nothing is transported. -/
def shearInnerRowCost (q : ℝ) : ℝ≥0∞ :=
  2 * (∫⁻ p in Ioo 0 (lowerShearThreshold q),
      ‖shearDifference p q‖ₑ * ENNReal.ofReal (|p - horizontalShearMap p q| ^ (1 / 2 : ℝ))) +
    ∫⁻ p in Ioo (horizontalShearMap 0 q) 1,
      ‖shearDifference p q‖ₑ * ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ))

/-- The cost of a row `q > 0` in the middle region `1 ≤ |p| ≤ m` (Chen and Hou, Part I,
(B.51)-(B.53)): `2 ∫_{h_c^+(q)}^{m} |Δ(p, q)| |p - T_y(p, q)|^{1/2} dp +
∫_1^{T_y(m, q)} |Δ(p, q)| (2p)^{1/2} dp`, the second integral up to `m` when `h_c^+(q) ≥ m`. -/
def shearMidRowCost (m q : ℝ) : ℝ≥0∞ :=
  2 * (∫⁻ p in Ioo (upperShearThreshold q) m,
      ‖shearDifference p q‖ₑ * ENNReal.ofReal (|p - horizontalShearMap p q| ^ (1 / 2 : ℝ))) +
    ∫⁻ p in Ioo 1 (shearMidEdge m q),
      ‖shearDifference p q‖ₑ * ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ))

/-- `Δ(·, q)` is continuous for `q ≠ 0`. -/
theorem continuous_shearDifference_left {q : ℝ} (hq : q ≠ 0) :
    Continuous fun p ↦ shearDifference p q := by
  have h : ∀ c : ℝ, Continuous fun p ↦ shearDensity (p + c) q := fun c ↦ by
    simp only [shearDensity_comm _ q]
    exact ((continuous_shearDensity_right hq).comp (continuous_id.add continuous_const)).neg
  simp only [shearDifference, sub_eq_add_neg (_ : ℝ) 1]
  exact (h 1).sub (h (-1))

/-- The odd fold of a `1/2`-Hölder function on `[-m, m]`: `h(p) - h(-p)` is `1/2`-Hölder on
`[0, m]` with twice the constant. -/
theorem holderOnWith_sub_neg {m : ℝ} {h : ℝ → ℝ} {C : ℝ≥0}
    (hh : HolderOnWith C (1 / 2) h (Icc (-m) m)) :
    HolderOnWith (2 * C) (1 / 2) (fun p ↦ h p - h (-p)) (Icc 0 m) := by
  intro t ht t' ht'
  have h₁ : t ∈ Icc (-m) m := ⟨by linarith [ht.1, ht.2], ht.2⟩
  have h₁' : t' ∈ Icc (-m) m := ⟨by linarith [ht'.1, ht'.2], ht'.2⟩
  have h₂ : -t ∈ Icc (-m) m := ⟨by linarith [ht.2], by linarith [ht.1, ht.2]⟩
  have h₂' : -t' ∈ Icc (-m) m := ⟨by linarith [ht'.2], by linarith [ht'.1, ht'.2]⟩
  calc edist (h t - h (-t)) (h t' - h (-t'))
      ≤ edist (h t) (h t') + edist (h (-t)) (h (-t')) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, ← edist_neg_neg (h (-t))]
        exact edist_add_add_le _ _ _ _
    _ ≤ C * edist t t' ^ ((1 / 2 : ℝ≥0) : ℝ) + C * edist (-t) (-t') ^ ((1 / 2 : ℝ≥0) : ℝ) :=
        add_le_add (hh t h₁ t' h₁') (hh (-t) h₂ (-t') h₂')
    _ = (2 * C : ℝ≥0) * edist t t' ^ ((1 / 2 : ℝ≥0) : ℝ) := by
        rw [edist_neg_neg, ENNReal.coe_mul, ENNReal.coe_ofNat]
        ring

/-- The odd fold is small near `0`: `|h(p) - h(-p)| ≤ C (2p)^{1/2}` for `0 ≤ p ≤ m`. -/
theorem abs_sub_neg_le {m : ℝ} {h : ℝ → ℝ} {C : ℝ≥0} (hh : HolderOnWith C (1 / 2) h (Icc (-m) m))
    {p : ℝ} (hp : p ∈ Icc 0 m) : |h p - h (-p)| ≤ C * (2 * p) ^ (1 / 2 : ℝ) := by
  have := hh.dist_le (x := p) (y := -p) ⟨by linarith [hp.1, hp.2], hp.2⟩
    ⟨by linarith [hp.2], by linarith [hp.1, hp.2]⟩
  rwa [Real.dist_eq, Real.dist_eq, show p - -p = 2 * p by ring,
    abs_of_nonneg (by linarith [hp.1] : (0 : ℝ) ≤ 2 * p),
    show ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 by norm_num] at this

/-- The bound of an integral by the lintegral of the norm of the integrand. -/
theorem ofReal_abs_intervalIntegral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal |∫ x in a..b, f x| ≤ ∫⁻ x in Ioc a b, ‖f x‖ₑ := by
  rw [intervalIntegral.integral_of_le hab, ← Real.enorm_eq_ofReal_abs]
  exact enorm_integral_le_lintegral_enorm _

/-- The inner balanced interval `[0, T_y(0, q)]` of a row `q > 0`, `3q² < 1`. -/
private theorem abs_integral_inner_le {q : ℝ} (hq : 0 < q) (h3 : 3 * q ^ 2 < 1) {G : ℝ → ℝ}
    {C : ℝ≥0} (hG : HolderOnWith C (1 / 2) G (Icc 0 (horizontalShearMap 0 q))) :
    ENNReal.ofReal |∫ p in (0 : ℝ)..horizontalShearMap 0 q, shearDifference p q * G p| ≤
      C * ∫⁻ p in Ioo 0 (lowerShearThreshold q),
        ‖shearDifference p q‖ₑ * ENNReal.ofReal (|p - horizontalShearMap p q| ^ (1 / 2 : ℝ)) := by
  set c := lowerShearThreshold q with hc
  set A := horizontalShearMap 0 q with hA
  have hc0 : 0 < c := lowerShearThreshold_pos hq.le h3
  have hcA : c < A := lowerShearThreshold_lt_horizontalShearMap hq h3 le_rfl hc0
  have hA1 : A < 1 := horizontalShearMap_lt_one hq h3 le_rfl hc0
  have hdom : ∀ x ∈ Ico 0 c, (x, q) ∈ lowerShearDomain := fun x hx ↦ ⟨hx.1, hq, h3, hx.2⟩
  rw [intervalIntegral.integral_of_le (hc0.trans hcA).le, ← integral_Icc_eq_integral_Ioc]
  have h := abs_setIntegral_Icc_mul_le_left (k := fun p ↦ shearDifference p q)
    (Ψ := horizontalShearPotential q) (T := fun p ↦ horizontalShearMap p q) (G := G)
    hc0.le hcA.le (continuous_shearDifference_left hq.ne').continuousOn
    (fun x _ ↦ hasDerivAt_horizontalShearPotential hq.ne' x)
    (by
      obtain ⟨hd, hr⟩ := lower_radicand hq h3 le_rfl hc0
      exact (horizontalShearPotential_horizontalShearMap hq.ne' hd.ne hr).symm)
    (fun x hx ↦ shearDifference_nonpos_of_lt_lowerShearThreshold hq hx.1 hx.2)
    (fun x hx ↦ shearDifference_nonneg_of_lowerShearThreshold_lt hq hx.1
      (hx.2.trans_lt (hA1.trans_le (one_le_upperShearThreshold hq.le))))
    (measurable_horizontalShearMap_left q)
    (fun x hx ↦ ⟨lowerShearThreshold_lt_horizontalShearMap hq h3 hx.1 hx.2,
      antitoneOn_horizontalShearMap_left (hdom 0 ⟨le_rfl, hc0⟩) (hdom x hx) hx.1⟩)
    (fun x hx ↦ by
      obtain ⟨hd, hr⟩ := lower_radicand hq h3 hx.1 hx.2
      exact horizontalShearPotential_horizontalShearMap hq.ne' hd.ne hr) hG
  refine h.trans_eq ?_
  congr 1
  rw [setLIntegral_congr (Ioo_ae_eq_Ico (μ := volume) (a := 0) (b := c)).symm]
  refine setLIntegral_congr_fun measurableSet_Ioo fun x _ ↦ ?_
  rw [abs_sub_comm]

/-- The middle balanced interval `[T_y(m, q), m]` of a row `q > 0` with `h_c^+(q) < m`. -/
private theorem abs_integral_mid_le {m q : ℝ} (hq : 0 < q) (hm : upperShearThreshold q < m)
    {G : ℝ → ℝ} {C : ℝ≥0} (hG : HolderOnWith C (1 / 2) G (Icc (horizontalShearMap m q) m)) :
    ENNReal.ofReal |∫ p in horizontalShearMap m q..m, shearDifference p q * G p| ≤
      C * ∫⁻ p in Ioo (upperShearThreshold q) m,
        ‖shearDifference p q‖ₑ * ENNReal.ofReal (|p - horizontalShearMap p q| ^ (1 / 2 : ℝ)) := by
  set c := upperShearThreshold q with hc
  set B := horizontalShearMap m q with hB
  have hmD : (m, q) ∈ upperShearDomain := ⟨hq, hm⟩
  have hBc : B < c := horizontalShearMap_lt_upperShearThreshold hmD
  have h1B : 1 < B := one_lt_horizontalShearMap hmD
  rw [intervalIntegral.integral_of_le (hBc.trans hm).le, ← integral_Icc_eq_integral_Ioc]
  have h := abs_setIntegral_Icc_mul_le_right (k := fun p ↦ -shearDifference p q)
    (Ψ := fun t ↦ -horizontalShearPotential q t) (T := fun p ↦ horizontalShearMap p q) (G := G)
    hBc.le hm.le (continuous_shearDifference_left hq.ne').neg.continuousOn
    (fun x _ ↦ (hasDerivAt_horizontalShearPotential hq.ne' x).neg)
    (by
      obtain ⟨hd, hr⟩ := upper_radicand hq hm
      rw [horizontalShearPotential_horizontalShearMap hq.ne' hd.ne' hr])
    (fun x hx ↦ neg_nonpos.2 (shearDifference_nonneg_of_lowerShearThreshold_lt hq
      ((lowerShearThreshold_le_one hq.le).trans_lt (h1B.trans_le hx.1)) hx.2))
    (fun x hx ↦ neg_nonneg.2 (shearDifference_nonpos_of_upperShearThreshold_lt hq hx.1))
    (measurable_horizontalShearMap_left q)
    (fun y hy ↦ ⟨antitoneOn_horizontalShearMap_left_upper (⟨hq, hy.1⟩ : (y, q) ∈ upperShearDomain)
      hmD hy.2, horizontalShearMap_lt_upperShearThreshold ⟨hq, hy.1⟩⟩)
    (fun y hy ↦ by
      obtain ⟨hd, hr⟩ := upper_radicand hq hy.1
      rw [horizontalShearPotential_horizontalShearMap hq.ne' hd.ne' hr]) hG
  simp only [neg_mul, integral_neg, abs_neg, enorm_neg] at h
  exact h.trans_eq (congrArg _ (setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := c)
    (b := m)).symm))

/-- **The row estimate** of Chen and Hou, Part I, Appendix B.2, (B.46)-(B.53). For a row `q > 0`,
`m ≥ 1` and `h` `1/2`-Hölder with constant `C` on `[-m, m]`,

`|∫_{-m}^{m} Δ(p, q) h(p) dp| ≤ C (shearInnerRowCost q + shearMidRowCost m q)`.

`Δ(·, q)` is odd, so the integral is `∫_0^m Δ(p, q) (h(p) - h(-p)) dp`; on `[0, T_y(0, q)]` and on
`[T_y(m, q), m]` (when `h_c^+(q) < m`) the kernel is balanced and is transported horizontally by
`T_y`, and in between `|h(p) - h(-p)| ≤ C (2p)^{1/2}`. -/
theorem abs_integral_shearDifference_mul_le_row {m q : ℝ} (hm : 1 ≤ m) (hq : 0 < q)
    {h : ℝ → ℝ} {C : ℝ≥0} (hh : HolderOnWith C (1 / 2) h (Icc (-m) m)) :
    ENNReal.ofReal |∫ p in Icc (-m) m, shearDifference p q * h p| ≤
      C * (shearInnerRowCost q + shearMidRowCost m q) := by
  set G : ℝ → ℝ := fun p ↦ h p - h (-p) with hG
  have hGh : HolderOnWith (2 * C) (1 / 2) G (Icc 0 m) := holderOnWith_sub_neg hh
  have hΔ := continuous_shearDifference_left hq.ne'
  have hhc : ContinuousOn h (Icc (-m) m) := hh.continuousOn (by norm_num)
  have hGc : ContinuousOn G (Icc 0 m) := hGh.continuousOn (by norm_num)
  have hm0 : (0 : ℝ) ≤ m := by linarith
  -- the odd fold
  have hfold : ∫ p in Icc (-m) m, shearDifference p q * h p =
      ∫ p in (0 : ℝ)..m, shearDifference p q * G p := by
    have := setIntegral_Icc_neg_eq hm0 (k := fun _ ↦ (1 : ℝ))
      (g := fun p ↦ shearDifference p q * h p) (fun _ ↦ rfl)
      (by simpa only [one_mul] using (hΔ.continuousOn.fun_mul hhc).integrableOn_Icc)
    simp only [one_mul] at this
    rw [this]
    refine intervalIntegral.integral_congr fun p _ ↦ ?_
    simp only [hG, shearDifference_neg_left]
    ring
  rw [hfold]
  -- the three pieces
  set A := horizontalShearMap 0 q with hA
  set B := shearMidEdge m q with hB
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hA1 : A ≤ 1 := by
    rw [hA, horizontalShearMap_zero_left]
    exact Real.sqrt_le_one.2 (by nlinarith [sq_nonneg q])
  have hB1 : 1 ≤ B ∧ B ≤ m := by
    simp only [hB, shearMidEdge]
    split_ifs with hc
    · have hmD : (m, q) ∈ upperShearDomain := ⟨hq, hc⟩
      exact ⟨(one_lt_horizontalShearMap hmD).le,
        ((horizontalShearMap_lt_upperShearThreshold hmD).trans hc).le⟩
    · exact ⟨hm, le_rfl⟩
  have hint : ∀ a b, 0 ≤ a → a ≤ b → b ≤ m →
      IntervalIntegrable (fun p ↦ shearDifference p q * G p) volume a b := fun a b ha hab hb ↦
    ((hΔ.continuousOn.mul hGc).mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 A le_rfl hA0 (hA1.trans hm))
      (hint A m hA0 (hA1.trans hm) le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals (hint A B hA0 (hA1.trans hB1.1) hB1.2)
      (hint B m (hA0.trans (hA1.trans hB1.1)) hB1.2 le_rfl)]
  set I := ∫⁻ p in Ioo 0 (lowerShearThreshold q),
    ‖shearDifference p q‖ₑ * ENNReal.ofReal (|p - horizontalShearMap p q| ^ (1 / 2 : ℝ))
  set J := ∫⁻ p in Ioo (upperShearThreshold q) m,
    ‖shearDifference p q‖ₑ * ENNReal.ofReal (|p - horizontalShearMap p q| ^ (1 / 2 : ℝ))
  set f : ℝ → ℝ≥0∞ := fun p ↦ ‖shearDifference p q‖ₑ * ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ))
  have h₁ : ENNReal.ofReal |∫ p in (0 : ℝ)..A, shearDifference p q * G p| ≤ 2 * C * I := by
    by_cases h3 : 3 * q ^ 2 < 1
    · have := abs_integral_inner_le hq h3 (hGh.mono (Icc_subset_Icc le_rfl (hA1.trans hm)))
      rwa [ENNReal.coe_mul, ENNReal.coe_ofNat] at this
    · have hA' : A = 0 := by
        rw [hA, horizontalShearMap_zero_left, Real.sqrt_eq_zero_of_nonpos (by linarith)]
      rw [hA', intervalIntegral.integral_same, abs_zero, ENNReal.ofReal_zero]
      exact zero_le
  have h₃ : ENNReal.ofReal |∫ p in B..m, shearDifference p q * G p| ≤ 2 * C * J := by
    by_cases hc : upperShearThreshold q < m
    · have hBe : B = horizontalShearMap m q := by simp only [hB, shearMidEdge, ite_eq_left hc]
      have := abs_integral_mid_le hq hc (G := G) (C := 2 * C)
        (hGh.mono (by rw [← hBe]; exact Icc_subset_Icc (hA0.trans (hA1.trans hB1.1)) le_rfl))
      rwa [ENNReal.coe_mul, ENNReal.coe_ofNat, ← hBe] at this
    · have hBe : B = m := by simp only [hB, shearMidEdge, ite_eq_right hc]
      rw [hBe, intervalIntegral.integral_same, abs_zero, ENNReal.ofReal_zero]
      exact zero_le
  have h₂ : ENNReal.ofReal |∫ p in A..B, shearDifference p q * G p| ≤
      C * ((∫⁻ p in Ioo A 1, f p) + ∫⁻ p in Ioo 1 B, f p) := by
    refine (ofReal_abs_intervalIntegral_le (hA1.trans hB1.1)).trans ?_
    have hpt : ∀ p ∈ Ioc A B, ‖shearDifference p q * G p‖ₑ ≤ C * f p := fun p hp ↦ by
      have hp' : p ∈ Icc 0 m := ⟨hA0.trans hp.1.le, hp.2.trans hB1.2⟩
      rw [enorm_mul, mul_comm (C : ℝ≥0∞), mul_assoc]
      gcongr
      rw [Real.enorm_eq_ofReal_abs, mul_comm, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (abs_sub_neg_le hh hp')
    calc ∫⁻ p in Ioc A B, ‖shearDifference p q * G p‖ₑ ≤ ∫⁻ p in Ioc A B, C * f p :=
          setLIntegral_mono' measurableSet_Ioc hpt
      _ ≤ (∫⁻ p in Ioc A 1, C * f p) + ∫⁻ p in Ioc 1 B, C * f p :=
          (lintegral_mono_set (Ioc_union_Ioc_eq_Ioc hA1 hB1.1).ge).trans (lintegral_union_le _ _ _)
      _ = C * ((∫⁻ p in Ioo A 1, f p) + ∫⁻ p in Ioo 1 B, f p) := by
          rw [setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := A) (b := 1)).symm,
            setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := 1) (b := B)).symm,
            lintegral_const_mul' _ _ ENNReal.coe_ne_top,
            lintegral_const_mul' _ _ ENNReal.coe_ne_top, mul_add]
  calc ENNReal.ofReal |(∫ p in (0 : ℝ)..A, shearDifference p q * G p) +
        ((∫ p in A..B, shearDifference p q * G p) + ∫ p in B..m, shearDifference p q * G p)|
      ≤ ENNReal.ofReal |∫ p in (0 : ℝ)..A, shearDifference p q * G p| +
          (ENNReal.ofReal |∫ p in A..B, shearDifference p q * G p| +
            ENNReal.ofReal |∫ p in B..m, shearDifference p q * G p|) :=
        (ofReal_abs_add_le _ _).trans (add_le_add le_rfl (ofReal_abs_add_le _ _))
    _ ≤ 2 * C * I + (C * ((∫⁻ p in Ioo A 1, f p) + ∫⁻ p in Ioo 1 B, f p) + 2 * C * J) := by
        gcongr
    _ = C * (shearInnerRowCost q + shearMidRowCost m q) := by
        simp only [shearInnerRowCost, shearMidRowCost, I, J, f, hA, hB]
        ring

end IncompressibleFlow.SharpHolder
