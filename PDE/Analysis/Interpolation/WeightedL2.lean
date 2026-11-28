/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Interpolation of two weighted `L²` bounds

If `‖Tu‖²` is at most `M₀ ‖u‖²` from `L²(w₀)` to `L²(v₀)` and at most `M₁ ‖u‖²` from `L²(w₁)` to
`L²(v₁)`, then it is at most `M₀^{1-θ} M₁^θ ‖u‖²` from `L²(w₀^{1-θ} w₁^θ)` to
`L²(v₀^{1-θ} v₁^θ)`, for `0 < θ < 1`. This is the case `p = 2` of the interpolation theorem of
Stein and Weiss with change of measures, proved here by the real method. On the Fourier side it
takes Sobolev estimates from integer orders to real orders. The statement does not mention the
operator: it is about two families of densities, `e x` on the source side and `g x` on the target
side, indexed by an arbitrary type, and it asks only for a splitting of each `x`. So
vector-valued functions and sums over components need no change. Exponents other than two, where
the splitting is not explicit, and the endpoint `M₀ = 0` are not treated.

## Main results

* `lintegral_kernel` (all `θ > 0`, all `z ≥ 0`): `∫₀^∞ τ^{-1-θ} (τ z / (1 + τ z)) dτ = k_θ z^θ`,
  with `k_θ = interpConst θ`.
* `interpConst_pos`, `interpConst_lt_top` (`0 < θ < 1`): `0 < k_θ < ∞`.
* `lintegral_rpow_mul_le` (all σ-finite measure spaces, all measurable weights, all
  `0 < θ < 1`, all `M₀ > 0`): `∫ r^θ v₀ g ≤ M₀^{1-θ} M₁^θ ∫ ρ^θ w₀ e`.

## How it works

Write `ρ = w₁/w₀` and `r = v₁/v₀`. For a parameter `q ≥ 0` split the argument as `u = u₀ + u₁`
with `u₁ = u / (1 + q ρ)`. The elementary inequality `λ/(1+λ) |a + b|² ≤ |a|² + λ |b|²` and the
two bounds give, for every `τ ≥ 0` and `q = τ M₁ / M₀`,

`∫ (τ r / (1 + τ r)) v₀ |Tu|² ≤ M₀ ∫ (q ρ / (1 + q ρ)) w₀ |u|²`

(`lintegral_kFrac_le`). Integrate in `τ` against `τ^{-1-θ} dτ` and exchange the integrals by
Tonelli's theorem (`lintegral_lintegral_kernel`). By scaling, the kernel integral is `k_θ z^θ`
with the same finite positive constant on both sides, so the constant cancels and the bound
remains. Only integrals of nonnegative functions appear.

## References

* E. M. Stein and G. Weiss, "Interpolation of operators with change of measures",
  *Trans. Amer. Math. Soc.* 87 (1958), 159-172.
  <https://doi.org/10.1090/S0002-9947-1958-0092943-6>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal NNReal

namespace PDE.Analysis.Interpolation

/-! ## The kernel -/

/-- The function `u ↦ u / (1 + u)` on `[0, ∞)`. -/
def kFrac (u : ℝ≥0) : ℝ≥0 := u / (1 + u)

/-- `u / (1 + u) ≤ u`. -/
theorem kFrac_le_self (u : ℝ≥0) : kFrac u ≤ u :=
  div_le_self (by positivity) (by simp)

/-- `u / (1 + u) ≤ 1`. -/
theorem kFrac_le_one (u : ℝ≥0) : kFrac u ≤ 1 :=
  div_le_one_of_le₀ (by simp) (by positivity)

/-- `u ↦ u / (1 + u)` is measurable. -/
theorem measurable_kFrac : Measurable kFrac :=
  measurable_id.div (measurable_const.add measurable_id)

/-- The kernel `τ ↦ τ^{-1-θ} (τ z / (1 + τ z))` of the real interpolation method. -/
def kernel (θ : ℝ) (z : ℝ≥0) (τ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (τ ^ (-1 - θ)) * (kFrac (τ.toNNReal * z) : ℝ≥0)

/-- The kernel is measurable in `τ`. -/
theorem measurable_kernel (θ : ℝ) (z : ℝ≥0) : Measurable (kernel θ z) :=
  (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
    (measurable_coe_nnreal_ennreal.comp
      (measurable_kFrac.comp (measurable_real_toNNReal.mul_const z)))

/-- The constant `k_θ = ∫₀^∞ τ^{-1-θ} (τ / (1 + τ)) dτ`. -/
def interpConst (θ : ℝ) : ℝ≥0∞ := ∫⁻ τ in Ioi 0, kernel θ 1 τ

/-- The kernel with the parameter `z` is a multiple of the kernel with the parameter one,
dilated by `z`. -/
theorem kernel_eq_mul {θ : ℝ} {z : ℝ≥0} (hz : 0 < z) {τ : ℝ} (hτ : 0 < τ) :
    kernel θ z τ = ENNReal.ofReal ((z : ℝ) ^ (1 + θ)) * kernel θ 1 (z * τ) := by
  have hz' : (0 : ℝ) < z := hz
  have h1 : ((z : ℝ) * τ).toNNReal * 1 = τ.toNNReal * z := by
    rw [mul_one, Real.toNNReal_mul hz'.le, Real.toNNReal_coe, mul_comm]
  have h2 : τ ^ (-1 - θ) = (z : ℝ) ^ (1 + θ) * ((z : ℝ) * τ) ^ (-1 - θ) := by
    have h0 : (1 + θ) + (-1 - θ) = 0 := by ring
    rw [Real.mul_rpow hz'.le hτ.le, ← mul_assoc, ← Real.rpow_add hz', h0, Real.rpow_zero,
      one_mul]
  unfold kernel
  rw [h1, h2, ENNReal.ofReal_mul (Real.rpow_nonneg hz'.le _), mul_assoc]

/-- The scaling of an integral over the half line. -/
theorem lintegral_Ioi_comp_mul {F : ℝ → ℝ≥0∞} (hF : Measurable F) {a : ℝ} (ha : 0 < a) :
    ∫⁻ τ in Ioi 0, F (a * τ) = ENNReal.ofReal a⁻¹ * ∫⁻ σ in Ioi 0, F σ := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  have h : (fun τ ↦ (Ioi (0 : ℝ)).indicator (fun τ ↦ F (a * τ)) τ) =
      fun τ ↦ (Ioi (0 : ℝ)).indicator F (a * τ) := by
    funext τ
    by_cases hτ : 0 < τ
    · rw [indicator_of_mem (mem_Ioi.2 hτ), indicator_of_mem (mem_Ioi.2 (mul_pos ha hτ))]
    · rw [indicator_of_notMem (fun h ↦ hτ (mem_Ioi.1 h)), indicator_of_notMem fun h ↦
        hτ ((mul_pos_iff_of_pos_left ha).1 (mem_Ioi.1 h))]
  rw [h, ← lintegral_map (hF.indicator measurableSet_Ioi) (measurable_const_mul a),
    Real.map_volume_mul_left ha.ne', lintegral_smul_measure, abs_of_pos (inv_pos.2 ha)]
  rfl

/-- **The kernel integral.** `∫₀^∞ τ^{-1-θ} (τ z / (1 + τ z)) dτ = k_θ z^θ` for `θ > 0`. -/
theorem lintegral_kernel {θ : ℝ} (hθ : 0 < θ) (z : ℝ≥0) :
    ∫⁻ τ in Ioi 0, kernel θ z τ = interpConst θ * (z : ℝ≥0∞) ^ θ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [kernel, kFrac, ENNReal.zero_rpow_of_pos hθ]
  have hz' : 0 < z := pos_iff_ne_zero.2 hz
  have hzr : (0 : ℝ) < z := hz'
  have h1 : ∫⁻ τ in Ioi 0, kernel θ z τ =
      ∫⁻ τ in Ioi 0, ENNReal.ofReal ((z : ℝ) ^ (1 + θ)) * kernel θ 1 (z * τ) :=
    setLIntegral_congr_fun measurableSet_Ioi fun τ hτ ↦ kernel_eq_mul hz' hτ
  rw [h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_Ioi_comp_mul (measurable_kernel θ 1) hzr, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hzr.le _), interpConst, mul_comm]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_pos hzr]
  congr 1
  rw [Real.rpow_add hzr, Real.rpow_one]
  field_simp

/-- The constant `k_θ` is finite for `0 < θ < 1`. -/
theorem interpConst_lt_top {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) : interpConst θ < ⊤ := by
  unfold interpConst
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, lintegral_union measurableSet_Ioi
    Ioc_disjoint_Ioi_same]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · have hint : IntegrableOn (fun τ : ℝ ↦ τ ^ (-θ)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioc fun τ hτ ↦ ?_)
      hint.setLIntegral_lt_top
    unfold kernel
    rw [mul_one]
    calc ENNReal.ofReal (τ ^ (-1 - θ)) * (kFrac τ.toNNReal : ℝ≥0)
        ≤ ENNReal.ofReal (τ ^ (-1 - θ)) * ENNReal.ofReal τ :=
          mul_le_mul' le_rfl (ENNReal.coe_le_coe.2 (kFrac_le_self _))
      _ = ENNReal.ofReal (τ ^ (-θ)) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hτ.1.le _)]
          congr 1
          rw [show -θ = (-1 - θ) + 1 by ring, Real.rpow_add hτ.1, Real.rpow_one]
  · have hint : IntegrableOn (fun τ : ℝ ↦ τ ^ (-1 - θ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun τ hτ ↦ ?_)
      hint.setLIntegral_lt_top
    unfold kernel
    calc ENNReal.ofReal (τ ^ (-1 - θ)) * (kFrac (τ.toNNReal * 1) : ℝ≥0)
        ≤ ENNReal.ofReal (τ ^ (-1 - θ)) * 1 :=
          mul_le_mul' le_rfl (by exact_mod_cast kFrac_le_one _)
      _ = _ := mul_one _

/-- The constant `k_θ` is positive. -/
theorem interpConst_pos (θ : ℝ) : 0 < interpConst θ := by
  unfold interpConst
  rw [lintegral_pos_iff_support (measurable_kernel θ 1)]
  have hsub : Ioi (0 : ℝ) ⊆ support (kernel θ 1) := by
    intro τ hτ
    have hτ' : (0 : ℝ) < τ := hτ
    have h1 : 0 < τ.toNNReal := Real.toNNReal_pos.2 hτ'
    have h2 : kFrac (τ.toNNReal * 1) ≠ 0 := by
      rw [mul_one, kFrac]
      exact (div_pos h1 (by positivity)).ne'
    have h3 : ENNReal.ofReal (τ ^ (-1 - θ)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hτ' _)).ne'
    exact mul_ne_zero h3 (by exact_mod_cast h2)
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Measure.restrict_apply measurableSet_Ioi, inter_self, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-! ## The interpolated bound -/

section Main

variable {α β X : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- Tonelli's theorem and the kernel integral: integrating the kernel with the parameter `z c`
against `τ` leaves `k_θ (z c)^θ`. -/
theorem lintegral_lintegral_kernel {γ : Type*} [MeasurableSpace γ] {κ : Measure γ} [SFinite κ]
    {θ : ℝ} (hθ : 0 < θ) {z : γ → ℝ≥0} (hz : Measurable z) {G : γ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ τ in Ioi 0, ∫⁻ c, kernel θ (z c) τ * G c ∂κ =
      interpConst θ * ∫⁻ c, (z c : ℝ≥0∞) ^ θ * G c ∂κ := by
  have hk : Measurable fun p : ℝ × γ ↦ kernel θ (z p.2) p.1 :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul
      (measurable_coe_nnreal_ennreal.comp (measurable_kFrac.comp
        ((measurable_real_toNNReal.comp measurable_fst).mul (hz.comp measurable_snd))))
  have hm : Measurable (uncurry fun (τ : ℝ) (c : γ) ↦ kernel θ (z c) τ * G c) :=
    hk.mul (hG.comp measurable_snd)
  have hf : Measurable fun c ↦ ((z c : ℝ≥0) : ℝ≥0∞) ^ θ * G c :=
    ((measurable_coe_nnreal_ennreal.comp hz).pow_const θ).mul hG
  rw [lintegral_lintegral_swap hm.aemeasurable, ← lintegral_const_mul _ hf]
  refine lintegral_congr fun c ↦ ?_
  rw [lintegral_mul_const _ (measurable_kernel θ (z c)), lintegral_kernel hθ, mul_assoc]

variable {e : X → α → ℝ≥0∞} {g : X → β → ℝ≥0∞} {w₀ ρ : α → ℝ≥0} {v₀ r : β → ℝ≥0}
  {M₀ M₁ : ℝ≥0}

/-- The inequality for one value of the parameter: with `q = τ M₁ / M₀`,
`∫ (τ r / (1 + τ r)) v₀ g ≤ M₀ ∫ (q ρ / (1 + q ρ)) w₀ e`. -/
theorem lintegral_kFrac_le (hem : ∀ x, Measurable (e x)) (hgm : ∀ x, Measurable (g x))
    (hw₀ : Measurable w₀) (hρ : Measurable ρ) (hv₀ : Measurable v₀) (hr : Measurable r)
    (hM₀ : M₀ ≠ 0)
    (h0 : ∀ x, ∫⁻ y, v₀ y * g x y ∂ν ≤ M₀ * ∫⁻ a, w₀ a * e x a ∂μ)
    (h1 : ∀ x, ∫⁻ y, v₀ y * r y * g x y ∂ν ≤ M₁ * ∫⁻ a, w₀ a * ρ a * e x a ∂μ)
    (hsplit : ∀ x, ∀ q : ℝ≥0, ∃ x₀ x₁ : X,
      (∀ᵐ a ∂μ, e x₀ a ≤ ((kFrac (q * ρ a) ^ 2 : ℝ≥0) : ℝ≥0∞) * e x a) ∧
      (∀ᵐ a ∂μ, e x₁ a ≤ ((((1 + q * ρ a)⁻¹) ^ 2 : ℝ≥0) : ℝ≥0∞) * e x a) ∧
      ∀ᵐ y ∂ν, ∀ l : ℝ≥0, (kFrac l : ℝ≥0∞) * g x y ≤ g x₀ y + l * g x₁ y)
    (x : X) (τ : ℝ≥0) :
    ∫⁻ y, (kFrac (τ * r y) : ℝ≥0∞) * (v₀ y * g x y) ∂ν ≤
      M₀ * ∫⁻ a, (kFrac (τ * (M₁ / M₀ * ρ a)) : ℝ≥0∞) * (w₀ a * e x a) ∂μ := by
  set q : ℝ≥0 := τ * (M₁ / M₀) with hq
  have hτq : τ * M₁ = M₀ * q := by
    rw [hq]
    field_simp
  obtain ⟨x₀, x₁, he0, he1, hg⟩ := hsplit x q
  have hmv (z : X) : Measurable fun y ↦ (v₀ y : ℝ≥0∞) * g z y :=
    (measurable_coe_nnreal_ennreal.comp hv₀).mul (hgm z)
  have hmvr (z : X) : Measurable fun y ↦ (v₀ y : ℝ≥0∞) * r y * g z y :=
    ((measurable_coe_nnreal_ennreal.comp hv₀).mul (measurable_coe_nnreal_ennreal.comp hr)).mul
      (hgm z)
  have hmw : Measurable fun a ↦ (w₀ a : ℝ≥0∞) * e x a :=
    (measurable_coe_nnreal_ennreal.comp hw₀).mul (hem x)
  -- the identity `M₀ d² + τ M₁ ρ c² = M₀ d` for `d = qρ/(1+qρ)` and `c = 1/(1+qρ)`
  have hid (a : α) : M₀ * kFrac (q * ρ a) ^ 2 + τ * M₁ * (ρ a * ((1 + q * ρ a)⁻¹) ^ 2) =
      M₀ * kFrac (q * ρ a) := by
    rw [hτq, kFrac]
    have hne : (1 + q * ρ a) ≠ 0 := by positivity
    field_simp
    ring
  calc ∫⁻ y, (kFrac (τ * r y) : ℝ≥0∞) * (v₀ y * g x y) ∂ν
      ≤ ∫⁻ y, ((v₀ y : ℝ≥0∞) * g x₀ y + τ * ((v₀ y : ℝ≥0∞) * r y * g x₁ y)) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hg] with y hy
        have h := mul_le_mul' (le_refl (v₀ y : ℝ≥0∞)) (hy (τ * r y))
        calc (kFrac (τ * r y) : ℝ≥0∞) * (v₀ y * g x y)
            = v₀ y * ((kFrac (τ * r y) : ℝ≥0∞) * g x y) := by ring
          _ ≤ v₀ y * (g x₀ y + ((τ * r y : ℝ≥0) : ℝ≥0∞) * g x₁ y) := h
          _ = _ := by
              push_cast
              ring
    _ = (∫⁻ y, (v₀ y : ℝ≥0∞) * g x₀ y ∂ν) + τ * ∫⁻ y, (v₀ y : ℝ≥0∞) * r y * g x₁ y ∂ν := by
        rw [lintegral_add_left (hmv x₀), lintegral_const_mul _ (hmvr x₁)]
    _ ≤ M₀ * (∫⁻ a, (w₀ a : ℝ≥0∞) * e x₀ a ∂μ) +
          τ * (M₁ * ∫⁻ a, (w₀ a : ℝ≥0∞) * ρ a * e x₁ a ∂μ) :=
        add_le_add (h0 x₀) (mul_le_mul' le_rfl (h1 x₁))
    _ ≤ M₀ * (∫⁻ a, ((kFrac (q * ρ a) ^ 2 : ℝ≥0) : ℝ≥0∞) * ((w₀ a : ℝ≥0∞) * e x a) ∂μ) +
          τ * (M₁ * ∫⁻ a, ((ρ a * ((1 + q * ρ a)⁻¹) ^ 2 : ℝ≥0) : ℝ≥0∞) *
            ((w₀ a : ℝ≥0∞) * e x a) ∂μ) := by
        refine add_le_add (mul_le_mul' le_rfl (lintegral_mono_ae ?_))
          (mul_le_mul' le_rfl (mul_le_mul' le_rfl (lintegral_mono_ae ?_)))
        · filter_upwards [he0] with a ha
          calc (w₀ a : ℝ≥0∞) * e x₀ a
              ≤ w₀ a * (((kFrac (q * ρ a) ^ 2 : ℝ≥0) : ℝ≥0∞) * e x a) := mul_le_mul' le_rfl ha
            _ = _ := by ring
        · filter_upwards [he1] with a ha
          calc (w₀ a : ℝ≥0∞) * ρ a * e x₁ a
              ≤ w₀ a * ρ a * (((((1 + q * ρ a)⁻¹) ^ 2 : ℝ≥0) : ℝ≥0∞) * e x a) :=
                mul_le_mul' le_rfl ha
            _ = _ := by
                push_cast
                ring
    _ = ∫⁻ a, ((M₀ * kFrac (q * ρ a) ^ 2 + τ * M₁ * (ρ a * ((1 + q * ρ a)⁻¹) ^ 2) : ℝ≥0) :
          ℝ≥0∞) * ((w₀ a : ℝ≥0∞) * e x a) ∂μ := by
        have hm1 : Measurable fun a ↦ ((kFrac (q * ρ a) ^ 2 : ℝ≥0) : ℝ≥0∞) *
            ((w₀ a : ℝ≥0∞) * e x a) :=
          (measurable_coe_nnreal_ennreal.comp
            ((measurable_kFrac.comp (hρ.const_mul q)).pow_const 2)).mul hmw
        rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          ← lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          ← lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          ← lintegral_add_left (hm1.const_mul _)]
        refine lintegral_congr fun a ↦ ?_
        push_cast
        ring
    _ = ∫⁻ a, ((M₀ * kFrac (q * ρ a) : ℝ≥0) : ℝ≥0∞) * ((w₀ a : ℝ≥0∞) * e x a) ∂μ := by
        refine lintegral_congr fun a ↦ ?_
        rw [hid a]
    _ = M₀ * ∫⁻ a, (kFrac (τ * (M₁ / M₀ * ρ a)) : ℝ≥0∞) * (w₀ a * e x a) ∂μ := by
        rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
        refine lintegral_congr fun a ↦ ?_
        rw [hq, mul_assoc τ]
        push_cast
        ring

/-- **Interpolation of two weighted `L²` bounds.** Let `e x` and `g x` be measurable densities
on two σ-finite measure spaces, indexed by `x : X`, with
`∫ v₀ g ≤ M₀ ∫ w₀ e` and `∫ v₀ r g ≤ M₁ ∫ w₀ ρ e` for every `x`. Suppose that for every `x` and
every `q ≥ 0` there are `x₀` and `x₁` with `e x₀ ≤ (qρ/(1+qρ))² e x`, `e x₁ ≤ (1/(1+qρ))² e x`
and `λ/(1+λ) g x ≤ g x₀ + λ g x₁` for all `λ ≥ 0`. Then, for `0 < θ < 1`,
`∫ r^θ v₀ g ≤ M₀^{1-θ} M₁^θ ∫ ρ^θ w₀ e`.

For a linear operator `T`, with `e x = |x|²` and `g x = |T x|²`, the splitting is
`x₁ = x / (1 + qρ)`, `x₀ = x - x₁`. The proof integrates `lintegral_kFrac_le` in the parameter
against `τ^{-1-θ} dτ` and cancels the constant of `lintegral_kernel`. -/
theorem lintegral_rpow_mul_le [SFinite μ] [SFinite ν] (hem : ∀ x, Measurable (e x))
    (hgm : ∀ x, Measurable (g x)) (hw₀ : Measurable w₀) (hρ : Measurable ρ)
    (hv₀ : Measurable v₀) (hr : Measurable r) (hM₀ : M₀ ≠ 0)
    (h0 : ∀ x, ∫⁻ y, v₀ y * g x y ∂ν ≤ M₀ * ∫⁻ a, w₀ a * e x a ∂μ)
    (h1 : ∀ x, ∫⁻ y, v₀ y * r y * g x y ∂ν ≤ M₁ * ∫⁻ a, w₀ a * ρ a * e x a ∂μ)
    (hsplit : ∀ x, ∀ q : ℝ≥0, ∃ x₀ x₁ : X,
      (∀ᵐ a ∂μ, e x₀ a ≤ ((kFrac (q * ρ a) ^ 2 : ℝ≥0) : ℝ≥0∞) * e x a) ∧
      (∀ᵐ a ∂μ, e x₁ a ≤ ((((1 + q * ρ a)⁻¹) ^ 2 : ℝ≥0) : ℝ≥0∞) * e x a) ∧
      ∀ᵐ y ∂ν, ∀ l : ℝ≥0, (kFrac l : ℝ≥0∞) * g x y ≤ g x₀ y + l * g x₁ y)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (x : X) :
    ∫⁻ y, (r y : ℝ≥0∞) ^ θ * (v₀ y * g x y) ∂ν ≤
      (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ *
        ∫⁻ a, (ρ a : ℝ≥0∞) ^ θ * (w₀ a * e x a) ∂μ := by
  have hmv : Measurable fun y ↦ (v₀ y : ℝ≥0∞) * g x y :=
    (measurable_coe_nnreal_ennreal.comp hv₀).mul (hgm x)
  have hmw : Measurable fun a ↦ (w₀ a : ℝ≥0∞) * e x a :=
    (measurable_coe_nnreal_ennreal.comp hw₀).mul (hem x)
  -- the inequality for each value of the parameter, with the kernel
  have hτ (τ : ℝ) : ∫⁻ y, kernel θ (r y) τ * ((v₀ y : ℝ≥0∞) * g x y) ∂ν ≤
      M₀ * ∫⁻ a, kernel θ (M₁ / M₀ * ρ a) τ * ((w₀ a : ℝ≥0∞) * e x a) ∂μ := by
    have h := lintegral_kFrac_le hem hgm hw₀ hρ hv₀ hr hM₀ h0 h1 hsplit x τ.toNNReal
    have h' := mul_le_mul' (le_refl (ENNReal.ofReal (τ ^ (-1 - θ)))) h
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
      mul_comm (ENNReal.ofReal _) (M₀ : ℝ≥0∞), mul_assoc,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h'
    simpa only [kernel, mul_assoc] using h'
  have hint := lintegral_mono (μ := volume.restrict (Ioi (0 : ℝ))) hτ
  rw [lintegral_lintegral_kernel hθ0 hr hmv, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
    lintegral_lintegral_kernel hθ0 (hρ.const_mul _) hmw, ← mul_assoc,
    mul_comm (M₀ : ℝ≥0∞), mul_assoc] at hint
  have hcancel := (ENNReal.mul_le_mul_iff_right (interpConst_pos θ).ne'
    (interpConst_lt_top hθ0 hθ1).ne).1 hint
  refine hcancel.trans_eq ?_
  -- the constant `M₀ (M₁/M₀)^θ = M₀^{1-θ} M₁^θ`
  have hpt (a : α) : ((M₁ / M₀ * ρ a : ℝ≥0) : ℝ≥0∞) ^ θ * ((w₀ a : ℝ≥0∞) * e x a) =
      ((M₁ / M₀ : ℝ≥0) : ℝ≥0∞) ^ θ * ((ρ a : ℝ≥0∞) ^ θ * ((w₀ a : ℝ≥0∞) * e x a)) := by
    rw [ENNReal.coe_mul, ENNReal.mul_rpow_of_nonneg _ _ hθ0.le, mul_assoc]
  rw [lintegral_congr hpt, lintegral_const_mul' _ _
    (ENNReal.rpow_ne_top_of_nonneg hθ0.le ENNReal.coe_ne_top), ← mul_assoc]
  congr 1
  have hM₀' : (0 : ℝ) < M₀ := lt_of_le_of_ne M₀.2 fun h ↦ hM₀ (NNReal.coe_eq_zero.1 h.symm)
  rw [← ENNReal.coe_rpow_of_nonneg _ hθ0.le, ← ENNReal.coe_rpow_of_nonneg _ hθ0.le,
    ← ENNReal.coe_rpow_of_nonneg _ (by linarith : 0 ≤ 1 - θ), ← ENNReal.coe_mul,
    ← ENNReal.coe_mul]
  congr 1
  apply NNReal.coe_injective
  push_cast
  rw [Real.div_rpow M₁.coe_nonneg M₀.coe_nonneg, Real.rpow_sub hM₀', Real.rpow_one]
  have hne : (M₀ : ℝ) ^ θ ≠ 0 := (Real.rpow_pos_of_pos hM₀' θ).ne'
  field_simp

end Main

end PDE.Analysis.Interpolation
