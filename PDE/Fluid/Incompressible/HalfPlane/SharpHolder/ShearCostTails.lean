/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearCostCells
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainCostTails

/-!
# The tails of the shear column cost

The outer cost `C_out(m) = 4 ∫_m^∞ ∫_{s_c(p)}^∞ |Δ| |t - T|^{1/2}` is a lower integral over the
heights of the lower integrals over the columns (`shearVerticalOuterCost_eq`). Above the
threshold `0 ≤ T ≤ t`, so the density is at most `|Δ| t^{1/2}` (`shearColumnDensity_le_sqrt`).
Near the axis the two kernels are bounded separately, `∫_{p > 1} |Δ(p, t)| dp ≤ π/(2t)`, so the
heights `t ≤ a` cost at most `π √a` (`lintegral_shearColumnDensity_bottom_le`). For `t ≥ 3` the
density vanishes for `p ≥ 2t` and `|Δ| ≤ 58 p/t⁴` for `0 ≤ p ≤ 2t`, so the heights `t > R ≥ 3`
cost at most `232/√R` over all columns `p > 0` (`lintegral_shearColumnDensity_top_le`).

## Main results

* `shearVerticalOuterCost_eq`: `C_out(m)` as a lower integral over the heights.
* `shearColumnDensity_le_sqrt`: above the threshold the density is at most `|Δ| t^{1/2}`.
* `lintegral_Ioi_abs_shearDifference_le`: `∫_{p > 1} |Δ(p, t)| dp ≤ π/(2t)`.
* `lintegral_shearColumnDensity_bottom_le`: the heights `t ≤ a` cost at most `π √a`.
* `shearColumnDensity_eq_zero_of_le`, `abs_shearDifference_le_of_le`: for `t ≥ 3` the density
  vanishes for `p ≥ 2t`, and `|Δ(p, t)| ≤ 58 p/t⁴` for `0 ≤ p ≤ 2t`.
* `lintegral_shearColumnDensity_top_le`: for `R ≥ 3` the heights `t > R` cost at most `232/√R`
  over all columns `p > 0`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter PDE.Analysis
open scoped ENNReal Topology

namespace IncompressibleFlow.SharpHolder

/-- `C_out(m)` as a lower integral over the heights. -/
theorem shearVerticalOuterCost_eq (m : ℝ) :
    shearVerticalOuterCost m =
      4 * ∫⁻ t in Ioi 0, ∫⁻ p in Ioi m, shearColumnDensity p t := by
  rw [shearVerticalOuterCost]
  congr 1
  simp_rw [shearColumnCost_eq]
  exact lintegral_lintegral_swap (measurable_shearColumnDensity.aemeasurable)

/-- Above the threshold `0 ≤ T ≤ t`: the density is at most `|Δ| t^{1/2}`. -/
theorem shearColumnDensity_le_sqrt {p t : ℝ} (ht : 0 < t) :
    shearColumnDensity p t ≤ ENNReal.ofReal (|shearDifference p t| * Real.sqrt t) := by
  unfold shearColumnDensity
  by_cases hs : t ∈ Ioi (shearThreshold p)
  · rw [indicator_of_mem hs]
    have hQ := shearQuartic_neg_of_shearThreshold_lt hs
    have hT := shearMap_le_self_of_shearQuartic_nonpos ht hQ.le
    have hT0 := shearMap_nonneg (y₁ := p) ht
    rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_mul (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (by rw [abs_of_nonneg (by linarith)]; linarith)
  · rw [indicator_of_notMem hs]
    exact zero_le

/-- `∫_{p > c} 1/(2((p - d)² + t²)) dp ≤ π/(4t)` for `d ≤ c` and `t > 0`. -/
theorem lintegral_Ioi_inv_sq_add_le {c d t : ℝ} (hdc : d ≤ c) (ht : 0 < t) :
    ∫⁻ p in Ioi c, ENNReal.ofReal (1 / (2 * ((p - d) ^ 2 + t ^ 2))) ≤
      ENNReal.ofReal (Real.pi / (4 * t)) := by
  refine (lintegral_mono_set (Ioi_subset_Ioi hdc)).trans (le_of_eq ?_)
  have hlim : Tendsto (fun p : ℝ ↦ Real.arctan ((p - d) / t) / (2 * t)) atTop
      (𝓝 (Real.pi / 2 / (2 * t))) := by
    refine (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp ?_ |>.div_const _
    exact (tendsto_atTop_add_const_right _ (-d) tendsto_id).atTop_div_const ht |>.congr
      fun p ↦ by simp only [id]; ring
  rw [lintegral_Ioi_ofReal_deriv (g := fun p ↦ Real.arctan ((p - d) / t) / (2 * t))
    (fun p _ ↦ ?_) (fun p _ ↦ by positivity) hlim]
  · congr 1
    simp only [sub_self, zero_div, Real.arctan_zero]
    field_simp
    ring
  · have h := (((hasDerivAt_id' p).sub_const d).div_const t).arctan.div_const (2 * t)
    refine h.congr_deriv ?_
    field_simp
    ring

/-- The two kernels separately: `∫_{p > 1} |Δ(p, t)| dp ≤ π/(2t)`. -/
theorem lintegral_Ioi_abs_shearDifference_le {t : ℝ} (ht : 0 < t) :
    ∫⁻ p in Ioi (1 : ℝ), ENNReal.ofReal |shearDifference p t| ≤
      ENNReal.ofReal (Real.pi / (2 * t)) := by
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
  calc ∫⁻ p in Ioi (1 : ℝ), ENNReal.ofReal |shearDifference p t|
      ≤ ∫⁻ p in Ioi (1 : ℝ), (ENNReal.ofReal (1 / (2 * ((p - (-1)) ^ 2 + t ^ 2))) +
          ENNReal.ofReal (1 / (2 * ((p - 1) ^ 2 + t ^ 2)))) := lintegral_mono hpt
    _ ≤ (∫⁻ p in Ioi (1 : ℝ), ENNReal.ofReal (1 / (2 * ((p - (-1)) ^ 2 + t ^ 2)))) +
          ∫⁻ p in Ioi (1 : ℝ), ENNReal.ofReal (1 / (2 * ((p - 1) ^ 2 + t ^ 2))) :=
        (lintegral_add_left (by fun_prop) _).le
    _ ≤ ENNReal.ofReal (Real.pi / (4 * t)) + ENNReal.ofReal (Real.pi / (4 * t)) :=
        add_le_add (lintegral_Ioi_inv_sq_add_le (by norm_num) ht)
          (lintegral_Ioi_inv_sq_add_le le_rfl ht)
    _ = ENNReal.ofReal (Real.pi / (2 * t)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        ring

/-- **The bottom tail**: the heights `t ≤ a` cost at most `π √a`. -/
theorem lintegral_shearColumnDensity_bottom_le {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioc 0 a, ∫⁻ p in Ioi (1 : ℝ), shearColumnDensity p t ≤
      ENNReal.ofReal (Real.pi * Real.sqrt a) := by
  have hpt : ∀ t ∈ Ioc (0 : ℝ) a, ∫⁻ p in Ioi (1 : ℝ), shearColumnDensity p t ≤
      ENNReal.ofReal (Real.pi / 2 * (1 / Real.sqrt t)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    calc ∫⁻ p in Ioi (1 : ℝ), shearColumnDensity p t
        ≤ ∫⁻ p in Ioi (1 : ℝ), ENNReal.ofReal |shearDifference p t| *
            ENNReal.ofReal (Real.sqrt t) := by
          refine lintegral_mono fun p ↦ ?_
          rw [← ENNReal.ofReal_mul (abs_nonneg _)]
          exact shearColumnDensity_le_sqrt ht0
      _ = (∫⁻ p in Ioi (1 : ℝ), ENNReal.ofReal |shearDifference p t|) *
            ENNReal.ofReal (Real.sqrt t) := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.pi / (2 * t)) * ENNReal.ofReal (Real.sqrt t) := by
          gcongr
          exact lintegral_Ioi_abs_shearDifference_le ht0
      _ = ENNReal.ofReal (Real.pi / 2 * (1 / Real.sqrt t)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have hs := Real.sqrt_pos.2 ht0
          have e : Real.pi / (2 * t) * Real.sqrt t =
              Real.pi / (2 * (Real.sqrt t * Real.sqrt t)) * Real.sqrt t := by
            rw [Real.mul_self_sqrt ht0.le]
          rw [e]
          field_simp
  calc ∫⁻ t in Ioc 0 a, ∫⁻ p in Ioi (1 : ℝ), shearColumnDensity p t
      ≤ ∫⁻ t in Ioc 0 a, ENNReal.ofReal (Real.pi / 2 * (1 / Real.sqrt t)) :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ = ENNReal.ofReal (Real.pi * Real.sqrt a) := by
        rw [lintegral_Ioc_ofReal_deriv (g := fun t ↦ Real.pi * Real.sqrt t) ha.le
          (by fun_prop) (fun t ht ↦ ?_) (fun t ht ↦ by positivity)]
        · simp
        · have ht0 : 0 < t := ht.1
          refine ((Real.hasDerivAt_sqrt ht0.ne').const_mul Real.pi).congr_deriv ?_
          have hs := Real.sqrt_pos.2 ht0
          field_simp

/-- For `t ≥ 3`, the density vanishes for `p ≥ 2t`. -/
theorem shearColumnDensity_eq_zero_of_le {p t : ℝ} (ht : 3 ≤ t) (hp : 2 * t ≤ p) :
    shearColumnDensity p t = 0 := by
  refine shearColumnDensity_eq_zero (by linarith) ?_
  have h₁ : t ^ 2 + 1 ≤ (2 * t) ^ 2 := by nlinarith
  refine le_trans ?_ (shearQuartic_le_of_right h₁ (by linarith) hp (by linarith) le_rfl)
  simp only [shearQuartic]
  nlinarith [sq_nonneg (t ^ 2 - 2), sq_nonneg t]

/-- For `t ≥ 3` and `0 ≤ p ≤ 2t`, `|Δ(p, t)| ≤ 58 p/t⁴`. -/
theorem abs_shearDifference_le_of_le {p t : ℝ} (ht : 3 ≤ t) (hp₁ : 0 ≤ p) (hp : p ≤ 2 * t) :
    |shearDifference p t| ≤ 58 * p / t ^ 4 := by
  have ht0 : 0 < t := by linarith
  have h₁ : (p + 1) ^ 2 + t ^ 2 ≠ 0 := by positivity
  have h₂ : (p - 1) ^ 2 + t ^ 2 ≠ 0 := by positivity
  rw [shearDifference_eq h₁ h₂, abs_div, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < ((p + 1) ^ 2 + t ^ 2) ^ 2 * ((p - 1) ^ 2 + t ^ 2) ^ 2)]
  have hQ : |shearQuartic p t| ≤ 29 * t ^ 4 := by
    have hp2 : p ^ 2 ≤ 4 * t ^ 2 := by nlinarith
    have hp4 : p ^ 4 ≤ 16 * t ^ 4 := by nlinarith
    have ht2 : 9 ≤ t ^ 2 := by nlinarith
    have ht4 : 10 * t ^ 2 + 1 ≤ 2 * t ^ 4 := by
      nlinarith [mul_le_mul_of_nonneg_left ht2 (sq_nonneg t)]
    simp only [shearQuartic]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg p, sq_nonneg t, mul_nonneg (sq_nonneg p) (sq_nonneg t)]
  have hD : t ^ 8 ≤ ((p + 1) ^ 2 + t ^ 2) ^ 2 * ((p - 1) ^ 2 + t ^ 2) ^ 2 := by
    have e1 : t ^ 2 ≤ (p + 1) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (p + 1)]
    have e2 : t ^ 2 ≤ (p - 1) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (p - 1)]
    have e1' := pow_le_pow_left₀ (by positivity) e1 2
    have e2' := pow_le_pow_left₀ (by positivity) e2 2
    calc t ^ 8 = (t ^ 2) ^ 2 * (t ^ 2) ^ 2 := by ring
      _ ≤ _ := mul_le_mul e1' e2' (by positivity) (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have habs : |(-2 : ℝ)| * |p| = 2 * p := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p)]
    norm_num
  rw [habs]
  calc 2 * p * |shearQuartic p t| * t ^ 4 ≤ 2 * p * (29 * t ^ 4) * t ^ 4 := by gcongr
    _ = 58 * p * t ^ 8 := by ring
    _ ≤ 58 * p * (((p + 1) ^ 2 + t ^ 2) ^ 2 * ((p - 1) ^ 2 + t ^ 2) ^ 2) := by gcongr

/-- **The top tail**: for `R ≥ 3`, the heights `t > R` cost at most `232/√R` over all columns
`p > 0`. -/
theorem lintegral_shearColumnDensity_top_le {R : ℝ} (hR : 3 ≤ R) :
    ∫⁻ t in Ioi R, ∫⁻ p in Ioi (0 : ℝ), shearColumnDensity p t ≤
      ENNReal.ofReal (232 / Real.sqrt R) := by
  have hR0 : 0 < R := by linarith
  have hpt : ∀ t ∈ Ioi R, ∫⁻ p in Ioi (0 : ℝ), shearColumnDensity p t ≤
      ENNReal.ofReal (116 / (t * Real.sqrt t)) := by
    intro t ht
    have ht3 : 3 ≤ t := hR.trans (le_of_lt ht)
    have ht0 : 0 < t := by linarith
    have hsplit : ∫⁻ p in Ioi (0 : ℝ), shearColumnDensity p t ≤
        ∫⁻ p in Ioc (0 : ℝ) (2 * t), shearColumnDensity p t := by
      have hsub : Ioi (0 : ℝ) ⊆ Ioc (0 : ℝ) (2 * t) ∪ Ioi (2 * t) := by
        intro p hp
        rcases le_or_gt p (2 * t) with h | h
        · exact Or.inl ⟨hp, h⟩
        · exact Or.inr h
      have h0 : ∫⁻ p in Ioi (2 * t), shearColumnDensity p t = 0 := by
        rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ ↦ 0) fun p hp ↦
          shearColumnDensity_eq_zero_of_le ht3 (le_of_lt hp)]
        simp
      calc ∫⁻ p in Ioi (0 : ℝ), shearColumnDensity p t
          ≤ ∫⁻ p in Ioc (0 : ℝ) (2 * t) ∪ Ioi (2 * t), shearColumnDensity p t :=
            lintegral_mono_set hsub
        _ ≤ _ := (lintegral_union_le _ _ _).trans (by rw [h0, add_zero])
    refine hsplit.trans ?_
    calc ∫⁻ p in Ioc (0 : ℝ) (2 * t), shearColumnDensity p t
        ≤ ∫⁻ p in Ioc (0 : ℝ) (2 * t), ENNReal.ofReal (58 * Real.sqrt t / t ^ 4 * p) := by
          refine setLIntegral_mono' measurableSet_Ioc fun p hp ↦ ?_
          refine (shearColumnDensity_le_sqrt ht0).trans (ENNReal.ofReal_le_ofReal ?_)
          have := abs_shearDifference_le_of_le ht3 hp.1.le hp.2
          calc |shearDifference p t| * Real.sqrt t ≤ 58 * p / t ^ 4 * Real.sqrt t :=
                mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
            _ = 58 * Real.sqrt t / t ^ 4 * p := by ring
      _ = ENNReal.ofReal (58 * Real.sqrt t / t ^ 4 * (((2 * t) ^ 2 - 0 ^ 2) / 2)) := by
          rw [lintegral_Ioc_ofReal_deriv (g := fun p ↦ 58 * Real.sqrt t / t ^ 4 * (p ^ 2 / 2))
            (by linarith) (by fun_prop) (fun p _ ↦ ?_) (fun p hp ↦ ?_)]
          · congr 1
            ring
          · refine ((((hasDerivAt_pow 2 p).div_const 2).const_mul
              (58 * Real.sqrt t / t ^ 4))).congr_deriv ?_
            ring
          · have : 0 < p := by linarith [hp.1]
            positivity
      _ ≤ ENNReal.ofReal (116 / (t * Real.sqrt t)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hs := Real.sqrt_pos.2 ht0
          have hs2 := Real.sq_sqrt ht0.le
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have : 58 * Real.sqrt t * (((2 * t) ^ 2 - 0 ^ 2) / 2) * (t * Real.sqrt t) =
              116 * t ^ 3 * Real.sqrt t ^ 2 := by ring
          rw [this, hs2]
          exact le_of_eq (by ring)
  calc ∫⁻ t in Ioi R, ∫⁻ p in Ioi (0 : ℝ), shearColumnDensity p t
      ≤ ∫⁻ t in Ioi R, ENNReal.ofReal (116 / (t * Real.sqrt t)) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal (232 / Real.sqrt R) := by
        rw [lintegral_Ioi_div_mul_sqrt hR0 (by norm_num)]
        norm_num

end IncompressibleFlow.SharpHolder
