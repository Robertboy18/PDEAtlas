/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearMassCells

/-!
# The tails of the envelopes of the horizontal estimate of `u_y`

Bounds of the upper envelope `U` and of the outer mass `W` (`shearUpperEnvelope`,
`shearOuterMass`) near the axis and at large heights, over all columns `p > 0`.

## Main results

* `shearUpperEnvelope_mono`, `shearOuterMass_anti`: `U` increases and `W` decreases with the
  height.
* `shearUpperEnvelope_le_add`, `shearOuterMass_le_add`: both split over consecutive ranges of
  heights.
* `lintegral_Ioi_zero_abs_shearDifference_le`: `∫_{p > 0} |Δ(p, t)| dp ≤ 3π/(4t)`.
* `shearUpperEnvelope_le_bottom`: `U(a) ≤ 6π √a`.
* `shearOuterMass_le_add_log`: `W(A) ≤ W(a) + (3π/4) log (a/A)` for `0 < A ≤ a`, with
  `√A log (a/A) ≤ 2 √a` (`sqrt_mul_log_div_le`).
* `lintegral_Ioi_zero_abs_shearDifference_le_top`: for `t ≥ 3`,
  `∫_{p > 0} |Δ(p, t)| dp ≤ 117/t²`.
* `shearOuterMass_le_top`: `W(R) ≤ 117/R` for `R ≥ 3`.
* `shearUpperEnvelope_le_top`: the heights above `R ≥ 3` add at most `4 · 232/√R` to `U`.
* `shearHolderEnvelope_le_bottom`, `shearHolderEnvelope_le_top`: the envelope of the horizontal
  estimate of `u_y` near the axis and at large heights.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter PDE.Analysis
open scoped ENNReal Topology

namespace IncompressibleFlow.SharpHolder

/-- The upper envelope `U` increases with the height. -/
theorem shearUpperEnvelope_mono {a b : ℝ} (h : a ≤ b) :
    shearUpperEnvelope a ≤ shearUpperEnvelope b := by
  rw [shearUpperEnvelope, shearUpperEnvelope]
  gcongr

/-- The outer mass `W` decreases with the height. -/
theorem shearOuterMass_anti {a b : ℝ} (h : a ≤ b) : shearOuterMass b ≤ shearOuterMass a :=
  lintegral_mono_set (Ioi_subset_Ioi h)

/-- The upper envelope over two ranges of heights (consecutive in the main use; the bound holds
for any two heights). -/
theorem shearUpperEnvelope_le_add {a b : ℝ} :
    shearUpperEnvelope b ≤ shearUpperEnvelope a +
      4 * ∫⁻ t in Ioc a b, ∫⁻ p in Ioi (0 : ℝ), shearColumnDensity p t := by
  rw [shearUpperEnvelope, shearUpperEnvelope, ← mul_add]
  gcongr
  exact (lintegral_mono_set Ioc_subset_Ioc_union_Ioc).trans (lintegral_union_le _ _ _)

/-- The outer mass over two consecutive ranges of heights. -/
theorem shearOuterMass_le_add {a b : ℝ} :
    shearOuterMass a ≤ (∫⁻ t in Ioc a b, ∫⁻ p in Ioi (0 : ℝ), ‖shearDifference p t‖ₑ) +
      shearOuterMass b := by
  rw [shearOuterMass, shearOuterMass]
  exact (lintegral_mono_set Ioi_subset_Ioc_union_Ioi).trans (lintegral_union_le _ _ _)

/-- The two kernels separately over all columns: `∫_{p > 0} |Δ(p, t)| dp ≤ 3π/(4t)`. -/
theorem lintegral_Ioi_zero_abs_shearDifference_le {t : ℝ} (ht : 0 < t) :
    ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal |shearDifference p t| ≤
      ENNReal.ofReal (3 * Real.pi / (4 * t)) := by
  have hpt : ∀ p, ENNReal.ofReal |shearDifference p t| ≤
      ENNReal.ofReal (1 / (2 * ((p - (-1)) ^ 2 + t ^ 2))) +
        ENNReal.ofReal (1 / (2 * ((p - 1) ^ 2 + t ^ 2))) := by
    intro p
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h₁ := abs_shearDensity_le (p + 1) t
    have h₂ := abs_shearDensity_le (p - 1) t
    rw [show p - -1 = p + 1 by ring]
    exact (abs_sub _ _).trans (add_le_add h₁ h₂)
  -- the second kernel over `p > 0` is at most its integral over the line
  have hK : ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal (1 / (2 * ((p - 1) ^ 2 + t ^ 2))) ≤
      ENNReal.ofReal (Real.pi / (2 * t)) := by
    have hsub : Ioi (0 : ℝ) ⊆ Ioc 0 1 ∪ Ioi 1 := by
      intro p hp
      rcases le_or_gt p 1 with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr h
    have h1 : ∫⁻ p in Ioc (0 : ℝ) 1, ENNReal.ofReal (1 / (2 * ((p - 1) ^ 2 + t ^ 2))) ≤
        ENNReal.ofReal (Real.pi / (4 * t)) := by
      rw [lintegral_Ioc_ofReal_deriv (g := fun p ↦ Real.arctan ((p - 1) / t) / (2 * t))
        zero_le_one (by fun_prop) (fun p _ ↦ ?_) (fun p _ ↦ by positivity)]
      · refine ENNReal.ofReal_le_ofReal ?_
        simp only [sub_self, zero_div, Real.arctan_zero, zero_sub]
        rw [neg_div, Real.arctan_neg, neg_div, neg_neg, div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith [Real.arctan_lt_pi_div_two (1 / t), Real.pi_pos]
      · have h := (((hasDerivAt_id' p).sub_const 1).div_const t).arctan.div_const (2 * t)
        refine h.congr_deriv ?_
        field_simp
        ring
    calc ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal (1 / (2 * ((p - 1) ^ 2 + t ^ 2)))
        ≤ ∫⁻ p in Ioc (0 : ℝ) 1 ∪ Ioi 1, ENNReal.ofReal (1 / (2 * ((p - 1) ^ 2 + t ^ 2))) :=
          lintegral_mono_set hsub
      _ ≤ ENNReal.ofReal (Real.pi / (4 * t)) + ENNReal.ofReal (Real.pi / (4 * t)) :=
          (lintegral_union_le _ _ _).trans (add_le_add h1 (lintegral_Ioi_inv_sq_add_le le_rfl ht))
      _ = ENNReal.ofReal (Real.pi / (2 * t)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          field_simp
          ring
  calc ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal |shearDifference p t|
      ≤ ∫⁻ p in Ioi (0 : ℝ), (ENNReal.ofReal (1 / (2 * ((p - (-1)) ^ 2 + t ^ 2))) +
          ENNReal.ofReal (1 / (2 * ((p - 1) ^ 2 + t ^ 2)))) := lintegral_mono hpt
    _ ≤ (∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal (1 / (2 * ((p - (-1)) ^ 2 + t ^ 2)))) +
          ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal (1 / (2 * ((p - 1) ^ 2 + t ^ 2))) :=
        (lintegral_add_left (by fun_prop) _).le
    _ ≤ ENNReal.ofReal (Real.pi / (4 * t)) + ENNReal.ofReal (Real.pi / (2 * t)) :=
        add_le_add (lintegral_Ioi_inv_sq_add_le (by norm_num) ht) hK
    _ = ENNReal.ofReal (3 * Real.pi / (4 * t)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        ring

/-- **The upper envelope near the axis**: `U(a) ≤ 6π √a`. -/
theorem shearUpperEnvelope_le_bottom {a : ℝ} (ha : 0 < a) :
    shearUpperEnvelope a ≤ ENNReal.ofReal (6 * Real.pi * Real.sqrt a) := by
  have hpt : ∀ t ∈ Ioc (0 : ℝ) a, ∫⁻ p in Ioi (0 : ℝ), shearColumnDensity p t ≤
      ENNReal.ofReal (3 * Real.pi / 4 * (1 / Real.sqrt t)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    calc ∫⁻ p in Ioi (0 : ℝ), shearColumnDensity p t
        ≤ ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal |shearDifference p t| *
            ENNReal.ofReal (Real.sqrt t) := by
          refine lintegral_mono fun p ↦ ?_
          rw [← ENNReal.ofReal_mul (abs_nonneg _)]
          exact shearColumnDensity_le_sqrt ht0
      _ = (∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal |shearDifference p t|) *
            ENNReal.ofReal (Real.sqrt t) := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (3 * Real.pi / (4 * t)) * ENNReal.ofReal (Real.sqrt t) := by
          gcongr
          exact lintegral_Ioi_zero_abs_shearDifference_le ht0
      _ = ENNReal.ofReal (3 * Real.pi / 4 * (1 / Real.sqrt t)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have hs := Real.sqrt_pos.2 ht0
          have e : 3 * Real.pi / (4 * t) * Real.sqrt t =
              3 * Real.pi / (4 * (Real.sqrt t * Real.sqrt t)) * Real.sqrt t := by
            rw [Real.mul_self_sqrt ht0.le]
          rw [e]
          field_simp
  rw [shearUpperEnvelope]
  calc 4 * ∫⁻ t in Ioc 0 a, ∫⁻ p in Ioi 0, shearColumnDensity p t
      ≤ 4 * ∫⁻ t in Ioc 0 a, ENNReal.ofReal (3 * Real.pi / 4 * (1 / Real.sqrt t)) := by
        have h : ∫⁻ t in Ioc 0 a, ∫⁻ p in Ioi 0, shearColumnDensity p t ≤
            ∫⁻ t in Ioc 0 a, ENNReal.ofReal (3 * Real.pi / 4 * (1 / Real.sqrt t)) :=
          setLIntegral_mono' measurableSet_Ioc hpt
        exact mul_le_mul_right h 4
    _ = 4 * ENNReal.ofReal (3 * Real.pi / 2 * Real.sqrt a) := by
        congr 1
        rw [lintegral_Ioc_ofReal_deriv (g := fun t ↦ 3 * Real.pi / 2 * Real.sqrt t) ha.le
          (by fun_prop) (fun t ht ↦ ?_) (fun t ht ↦ by positivity)]
        · simp
        · have ht0 : 0 < t := ht.1
          refine ((Real.hasDerivAt_sqrt ht0.ne').const_mul (3 * Real.pi / 2)).congr_deriv ?_
          have hs := Real.sqrt_pos.2 ht0
          field_simp
          ring
    _ = ENNReal.ofReal (6 * Real.pi * Real.sqrt a) := by
        rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- The mass between the heights `A ≤ a`: at most `(3π/4) log (a/A)`. -/
theorem lintegral_enorm_shearDifference_le_log {A a : ℝ} (hA : 0 < A) (hAa : A ≤ a) :
    ∫⁻ t in Ioc A a, ∫⁻ p in Ioi (0 : ℝ), ‖shearDifference p t‖ₑ ≤
      ENNReal.ofReal (3 * Real.pi / 4 * Real.log (a / A)) := by
  have hpt : ∀ t ∈ Ioc A a, ∫⁻ p in Ioi (0 : ℝ), ‖shearDifference p t‖ₑ ≤
      ENNReal.ofReal (3 * Real.pi / 4 * t⁻¹) := by
    intro t ht
    have ht0 : 0 < t := hA.trans ht.1
    refine le_trans (le_of_eq ?_) ((lintegral_Ioi_zero_abs_shearDifference_le ht0).trans
      (le_of_eq ?_))
    · refine setLIntegral_congr_fun measurableSet_Ioi fun p _ ↦ ?_
      rw [← ofReal_norm, Real.norm_eq_abs]
    · congr 1
      field_simp
  refine (setLIntegral_mono' measurableSet_Ioc hpt).trans (le_of_eq ?_)
  rw [lintegral_Ioc_ofReal_deriv (g := fun t ↦ 3 * Real.pi / 4 * Real.log t) hAa
    (fun t ht ↦ (continuousAt_const.mul (Real.continuousAt_log
      (hA.trans_le ht.1).ne')).continuousWithinAt) (fun t ht ↦ ?_)
    (fun t ht ↦ by have := hA.trans ht.1; positivity)]
  · congr 1
    rw [Real.log_div (by linarith) hA.ne']
    ring
  · exact (Real.hasDerivAt_log (hA.trans ht.1).ne').const_mul _

/-- **The outer mass below a height**: `W(A) ≤ W(a) + (3π/4) log (a/A)` for `0 < A ≤ a`. -/
theorem shearOuterMass_le_add_log {A a : ℝ} (hA : 0 < A) (hAa : A ≤ a) :
    shearOuterMass A ≤ ENNReal.ofReal (3 * Real.pi / 4 * Real.log (a / A)) + shearOuterMass a := by
  rw [shearOuterMass, shearOuterMass, ← Ioc_union_Ioi_eq_Ioi hAa]
  exact (lintegral_union_le _ _ _).trans
    (add_le_add (lintegral_enorm_shearDifference_le_log hA hAa) le_rfl)

/-- `√A log (a/A) ≤ 2 √a` for `A ≤ a` (for `A ≤ 0` the left side is `0`). -/
theorem sqrt_mul_log_div_le {A a : ℝ} (hAa : A ≤ a) :
    Real.sqrt A * Real.log (a / A) ≤ 2 * Real.sqrt a := by
  by_cases hA : 0 < A
  swap
  · rw [Real.sqrt_eq_zero'.mpr (not_lt.mp hA), zero_mul]
    positivity
  have ha : 0 < a := hA.trans_le hAa
  set y := Real.sqrt (a / A)
  have hy : 0 < y := Real.sqrt_pos.2 (div_pos ha hA)
  have hy2 : y ^ 2 = a / A := Real.sq_sqrt (div_pos ha hA).le
  have hlog : Real.log (a / A) = 2 * Real.log y := by
    rw [← hy2, Real.log_pow]
    norm_num
  have hl := Real.log_le_sub_one_of_pos hy
  have hsA := Real.sqrt_pos.2 hA
  have hya : Real.sqrt A * y = Real.sqrt a := by
    simp only [y]
    rw [← Real.sqrt_mul hA.le, mul_div_cancel₀ _ hA.ne']
  rw [hlog]
  nlinarith [mul_le_mul_of_nonneg_left hl hsA.le]

/-- For `t ≥ 3`, `∫_{p > 0} |Δ(p, t)| dp ≤ 117/t²`. -/
theorem lintegral_Ioi_zero_abs_shearDifference_le_top {t : ℝ} (ht : 3 ≤ t) :
    ∫⁻ p in Ioi (0 : ℝ), ‖shearDifference p t‖ₑ ≤ ENNReal.ofReal (117 / t ^ 2) := by
  have ht0 : 0 < t := by linarith
  have hsub : Ioi (0 : ℝ) ⊆ Ioc 0 (2 * t) ∪ Ioi (2 * t) := by
    intro p hp
    rcases le_or_gt p (2 * t) with h | h
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr h
  -- the near columns
  have h₁ : ∫⁻ p in Ioc (0 : ℝ) (2 * t), ‖shearDifference p t‖ₑ ≤ ENNReal.ofReal (116 / t ^ 2) := by
    calc ∫⁻ p in Ioc (0 : ℝ) (2 * t), ‖shearDifference p t‖ₑ
        ≤ ∫⁻ p in Ioc (0 : ℝ) (2 * t), ENNReal.ofReal (58 / t ^ 4 * p) := by
          refine setLIntegral_mono' measurableSet_Ioc fun p hp ↦ ?_
          rw [← ofReal_norm, Real.norm_eq_abs]
          refine ENNReal.ofReal_le_ofReal ((abs_shearDifference_le_of_le ht hp.1.le hp.2).trans
            (le_of_eq ?_))
          ring
      _ = ENNReal.ofReal (58 / t ^ 4 * ((2 * t) ^ 2 / 2) - 58 / t ^ 4 * (0 ^ 2 / 2)) := by
          rw [lintegral_Ioc_ofReal_deriv (g := fun p ↦ 58 / t ^ 4 * (p ^ 2 / 2)) (by linarith)
            (by fun_prop) (fun p _ ↦ ?_) (fun p hp ↦ by have := hp.1; positivity)]
          refine (((hasDerivAt_pow 2 p).div_const 2).const_mul (58 / t ^ 4)).congr_deriv ?_
          ring
      _ = ENNReal.ofReal (116 / t ^ 2) := by
          congr 1
          field_simp
          ring
  -- the far columns, where `Δ ≤ 0`
  have h₂ : ∫⁻ p in Ioi (2 * t), ‖shearDifference p t‖ₑ ≤ ENNReal.ofReal (1 / t ^ 2) := by
    have hint : Integrable (fun p ↦ shearDifference p t) :=
      (integrable_shearDensity_add ht0 1).sub (integrable_shearDensity_add ht0 (-1))
    have hneg : ∀ p ∈ Ioi (2 * t), shearDifference p t ≤ 0 := by
      intro p hp
      refine shearDifference_nonpos_of_shearQuartic_nonneg (by linarith [hp.out]) ht0 ?_
      have h₁ : t ^ 2 + 1 ≤ (2 * t) ^ 2 := by nlinarith
      refine le_trans ?_ (shearQuartic_le_of_right h₁ (by linarith) (le_of_lt hp) ht0.le le_rfl)
      simp only [shearQuartic]
      nlinarith [sq_nonneg (t ^ 2 - 2), sq_nonneg t]
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun p ↦ ENNReal.ofReal
      (-shearDifference p t)) fun p hp ↦ by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonpos (hneg p hp)],
      ← ofReal_integral_eq_lintegral_ofReal (f := fun p ↦ -shearDifference p t)
        hint.neg.integrableOn (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Ioi)
          fun p hp ↦ neg_nonneg.2 (hneg p hp))]
    refine ENNReal.ofReal_le_ofReal ?_
    have e₁ := integral_Ioi_shearDensity_add ht0 (2 * t) 1
    have e₂ := integral_Ioi_shearDensity_add ht0 (2 * t) (-1)
    rw [integral_neg, show ∫ p in Ioi (2 * t), shearDifference p t =
        (∫ p in Ioi (2 * t), shearDensity (p + 1) t) -
          ∫ p in Ioi (2 * t), shearDensity (p + -1) t by
      rw [← integral_sub (integrable_shearDensity_add ht0 1).integrableOn
        (integrable_shearDensity_add ht0 (-1)).integrableOn]
      rfl, e₁, e₂]
    have hd₁ : 0 < 2 * ((2 * t + 1) ^ 2 + t ^ 2) := by positivity
    have hd₂ : 0 < 2 * ((2 * t + -1) ^ 2 + t ^ 2) := by positivity
    rw [neg_sub, div_sub_div _ _ hd₂.ne' hd₁.ne', div_le_div_iff₀ (mul_pos hd₂ hd₁)
      (by positivity)]
    nlinarith [sq_nonneg t, sq_nonneg (t ^ 2), mul_pos ht0 ht0]
  calc ∫⁻ p in Ioi (0 : ℝ), ‖shearDifference p t‖ₑ
      ≤ ∫⁻ p in Ioc (0 : ℝ) (2 * t) ∪ Ioi (2 * t), ‖shearDifference p t‖ₑ :=
        lintegral_mono_set hsub
    _ ≤ ENNReal.ofReal (116 / t ^ 2) + ENNReal.ofReal (1 / t ^ 2) :=
        (lintegral_union_le _ _ _).trans (add_le_add h₁ h₂)
    _ = ENNReal.ofReal (117 / t ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The outer mass at large heights**: `W(R) ≤ 117/R` for `R ≥ 3`. -/
theorem shearOuterMass_le_top {R : ℝ} (hR : 3 ≤ R) :
    shearOuterMass R ≤ ENNReal.ofReal (117 / R) := by
  have hR0 : 0 < R := by linarith
  refine (setLIntegral_mono' measurableSet_Ioi fun t ht ↦
    lintegral_Ioi_zero_abs_shearDifference_le_top (hR.trans (le_of_lt ht))).trans (le_of_eq ?_)
  rw [lintegral_Ioi_ofReal_deriv (a := R) (l := 0) (g := fun t ↦ -(117 / t))
    (fun t ht ↦ ?_) (fun t ht ↦ by have := hR0.trans ht; positivity)
    (by simpa using (tendsto_const_nhds (x := (117 : ℝ))).div_atTop tendsto_id |>.neg)]
  · congr 1
    ring
  · have ht0 : 0 < t := hR0.trans_le ht
    refine ((hasDerivAt_const t (117 : ℝ)).div (hasDerivAt_id t) ht0.ne').neg.congr_deriv ?_
    simp only [id]
    field_simp
    ring

/-- **The upper envelope at large heights**: `U(A) ≤ U(R) + 4 · 232/√R` for `3 ≤ R`. -/
theorem shearUpperEnvelope_le_top {R A : ℝ} (hR : 3 ≤ R) :
    shearUpperEnvelope A ≤ shearUpperEnvelope R + ENNReal.ofReal (4 * (232 / Real.sqrt R)) := by
  refine (shearUpperEnvelope_le_add (a := R)).trans ?_
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  gcongr
  exact (lintegral_mono_set Ioc_subset_Ioi_self).trans (lintegral_shearColumnDensity_top_le hR)

/-- **The envelope near the axis**: for `0 < A ≤ a`, `U(a) ≤ U` and `W(a) ≤ M`, the envelope is at
most `√2 π + τ (U + 2 √2 √a (3π/2 + M))`. -/
theorem shearHolderEnvelope_le_bottom {τ A a U M : ℝ} (hτ : 0 ≤ τ) (hA : 0 < A) (hAa : A ≤ a)
    (hU0 : 0 ≤ U) (hM0 : 0 ≤ M) (hU : shearUpperEnvelope a ≤ ENNReal.ofReal U)
    (hW : shearOuterMass a ≤ ENNReal.ofReal M) :
    shearHolderEnvelope τ A ≤ ENNReal.ofReal (Real.sqrt 2 * Real.pi +
      τ * (U + 2 * Real.sqrt 2 * Real.sqrt a * (3 * Real.pi / 2 + M))) := by
  have hπ := Real.pi_pos
  have hL0 : 0 ≤ 3 * Real.pi / 4 * Real.log (a / A) :=
    mul_nonneg (by positivity) (Real.log_nonneg ((one_le_div hA).2 hAa))
  have hX : shearMassEnvelope A ≤ ENNReal.ofReal (Real.sqrt 2 * Real.pi) := by
    rw [shearMassEnvelope_eq hA]
    refine ENNReal.ofReal_le_ofReal (div_le_self (by positivity) ?_)
    have h₁ : 1 ≤ Real.sqrt (1 + A ^ 2) := Real.one_le_sqrt.2 (by nlinarith)
    exact Real.one_le_sqrt.2 (by linarith)
  have hO : ENNReal.ofReal (2 * (2 * A) ^ (1 / 2 : ℝ)) * shearOuterMass A ≤
      ENNReal.ofReal (2 * Real.sqrt 2 * Real.sqrt a * (3 * Real.pi / 2 + M)) := by
    have hW' : shearOuterMass A ≤ ENNReal.ofReal (3 * Real.pi / 4 * Real.log (a / A) + M) := by
      rw [ENNReal.ofReal_add hL0 hM0]
      exact (shearOuterMass_le_add_log hA hAa).trans (add_le_add le_rfl hW)
    calc ENNReal.ofReal (2 * (2 * A) ^ (1 / 2 : ℝ)) * shearOuterMass A
        ≤ ENNReal.ofReal (2 * (2 * A) ^ (1 / 2 : ℝ)) *
            ENNReal.ofReal (3 * Real.pi / 4 * Real.log (a / A) + M) := by gcongr
      _ ≤ ENNReal.ofReal (2 * Real.sqrt 2 * Real.sqrt a * (3 * Real.pi / 2 + M)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num)]
        have h₁ := sqrt_mul_log_div_le hAa
        have h₂ : Real.sqrt A ≤ Real.sqrt a := Real.sqrt_le_sqrt hAa
        have h₃ : Real.sqrt A * (3 * Real.pi / 4 * Real.log (a / A) + M) ≤
            Real.sqrt a * (3 * Real.pi / 2 + M) := by
          nlinarith [mul_le_mul_of_nonneg_left h₂ hM0, mul_le_mul_of_nonneg_left h₁ hπ.le]
        calc 2 * (Real.sqrt 2 * Real.sqrt A) * (3 * Real.pi / 4 * Real.log (a / A) + M)
            = 2 * Real.sqrt 2 * (Real.sqrt A * (3 * Real.pi / 4 * Real.log (a / A) + M)) := by
              ring
          _ ≤ 2 * Real.sqrt 2 * (Real.sqrt a * (3 * Real.pi / 2 + M)) := by gcongr
          _ = 2 * Real.sqrt 2 * Real.sqrt a * (3 * Real.pi / 2 + M) := by ring
  calc shearHolderEnvelope τ A
      ≤ ENNReal.ofReal (Real.sqrt 2 * Real.pi) + ENNReal.ofReal τ * (ENNReal.ofReal U +
          ENNReal.ofReal (2 * Real.sqrt 2 * Real.sqrt a * (3 * Real.pi / 2 + M))) := by
        unfold shearHolderEnvelope
        gcongr
        exact (shearUpperEnvelope_mono hAa).trans hU
    _ = _ := by
        rw [← ENNReal.ofReal_add hU0 (by positivity), ← ENNReal.ofReal_mul hτ,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- **The envelope at large heights**: for `3 ≤ R ≤ A` and `U(R) ≤ U`, the envelope is at most
`√2 π/√R + τ (U + 4 · 232/√R + 234 √2/√R)`. -/
theorem shearHolderEnvelope_le_top {τ A R U : ℝ} (hτ : 0 ≤ τ) (hR : 3 ≤ R) (hRA : R ≤ A)
    (hU0 : 0 ≤ U) (hU : shearUpperEnvelope R ≤ ENNReal.ofReal U) :
    shearHolderEnvelope τ A ≤ ENNReal.ofReal (Real.sqrt 2 * Real.pi / Real.sqrt R +
      τ * (U + 4 * (232 / Real.sqrt R) + 234 * Real.sqrt 2 / Real.sqrt R)) := by
  have hR0 : 0 < R := by linarith
  have hA : 0 < A := hR0.trans_le hRA
  have hsR := Real.sqrt_pos.2 hR0
  have hsRA : Real.sqrt R ≤ Real.sqrt A := Real.sqrt_le_sqrt hRA
  have hX : shearMassEnvelope A ≤ ENNReal.ofReal (Real.sqrt 2 * Real.pi / Real.sqrt R) := by
    rw [shearMassEnvelope_eq hA]
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by positivity) hsR ?_)
    exact hsRA.trans (Real.sqrt_le_sqrt (by linarith [Real.sqrt_nonneg (1 + A ^ 2)]))
  have hUA : shearUpperEnvelope A ≤ ENNReal.ofReal (U + 4 * (232 / Real.sqrt R)) := by
    rw [ENNReal.ofReal_add hU0 (by positivity)]
    exact (shearUpperEnvelope_le_top hR).trans (add_le_add hU le_rfl)
  have hO : ENNReal.ofReal (2 * (2 * A) ^ (1 / 2 : ℝ)) * shearOuterMass A ≤
      ENNReal.ofReal (234 * Real.sqrt 2 / Real.sqrt R) := by
    calc ENNReal.ofReal (2 * (2 * A) ^ (1 / 2 : ℝ)) * shearOuterMass A
        ≤ ENNReal.ofReal (2 * (2 * A) ^ (1 / 2 : ℝ)) * ENNReal.ofReal (117 / A) := by
          gcongr
          exact shearOuterMass_le_top (hR.trans hRA)
      _ ≤ ENNReal.ofReal (234 * Real.sqrt 2 / Real.sqrt R) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num)]
        calc 2 * (Real.sqrt 2 * Real.sqrt A) * (117 / A)
            = 234 * Real.sqrt 2 * (Real.sqrt A / A) := by ring
          _ = 234 * Real.sqrt 2 / Real.sqrt A := by rw [Real.sqrt_div_self']; ring
          _ ≤ 234 * Real.sqrt 2 / Real.sqrt R :=
              div_le_div_of_nonneg_left (by positivity) hsR hsRA
  calc shearHolderEnvelope τ A
      ≤ ENNReal.ofReal (Real.sqrt 2 * Real.pi / Real.sqrt R) + ENNReal.ofReal τ *
          (ENNReal.ofReal (U + 4 * (232 / Real.sqrt R)) +
            ENNReal.ofReal (234 * Real.sqrt 2 / Real.sqrt R)) := by
        unfold shearHolderEnvelope
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hτ,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

end IncompressibleFlow.SharpHolder
