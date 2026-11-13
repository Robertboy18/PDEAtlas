/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Rearrangement.Transport1D
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainMap

/-!
# The one-dimensional transport estimate of the localized strain kernel

Fix the height `s₂ > 0` and a localization `A ≥ 1/2` (the box half-width in units of the
distance of the two points). The kernel of the localized difference
`u_x(1/2, ·, A) - u_x(-1/2, ·, A)` on the line of height `s₂` is

`k_A(s₁) = 1{|s₁ + 1/2| ≤ A} K₁(s₁ + 1/2, s₂) - 1{|s₁ - 1/2| ≤ A} K₁(s₁ - 1/2, s₂)`,

`localStrainDifference A s₁ s₂` (Chen and Hou, Part I, (3.16)). It is even in `s₁`; on the half-line
`s₁ ≥ 0` it is nonnegative up to the threshold `c = max(1/2, min(f(s₂), A - 1/2))`
(`localStrainThreshold`, the threshold `s_c` of (3.18)), negative on `(c, A + 1/2]` and zero beyond,
with zero mass. The transport lemma (Part I, Lemma 3.6) bounds `∫_0^∞ k_A g` by the transport cost
of `k_A`. Our main result, `abs_setIntegral_localStrainDifference_mul_le`, is (3.18)-(3.24): the
localized cost is at most the cost

`M(s₂) = ∫_{f(s₂)}^∞ |Δ(s₁, s₂)| |T(s₁, s₂) - s₁|^{1/2} ds₁`

(`strainCost`) of the full kernel `Δ` with its transport map `T`.

## Main declarations

* `localStrainDifference`, `localStrainThreshold`, `strainCost`.
* `strainConstant b = (4/π) ∫_0^b M(s₂) ds₂`: the constant `C₁(b)` of Part I, Lemma 3.1, as an
  extended real; `monotone_strainConstant`.
* `abs_setIntegral_localStrainDifference_mul_le`: the half-line estimate
  `|∫_0^∞ k_A g| ≤ C M(s₂)` for `g` `1/2`-Hölder with constant `C` on `[0, A + 1/2]`.
* `abs_integral_localStrainDifference_mul_le`: the line estimate
  `|∫ k_A g| ≤ 2 C M(|s₂|)` for `s₂ ≠ 0`.

## How it works

We apply the transport lemma in its abstract form,
`PDE.Analysis.Rearrangement.IsBalancedKernel.abs_integral_mul_sub_le`, to `k_A` on the half-line
with the threshold `c`, and compare the resulting cost with the full cost by one comparison
argument. If `x ∈ (0, c)` is matched with `y ∈ (c, A + 1/2]` by the localized kernel, then
`y ≤ T(x)`: otherwise `[x, T(x)]` lies in `[0, A + 1/2]`, where `k_A ≤ Δ`, so
`∫_x^{T(x)} k_A ≤ ∫_x^{T(x)} Δ = 0`, while `∫_{T(x)}^{y} k_A < 0`, contradicting `∫_x^{y} k_A = 0`.
Since also `0 ≤ k_A ≤ Δ` on `[0, c]` and `c ≤ f`, the localized cost is at most the full cost on the
left side, which equals the full cost on the right side because `T` is an involution. The line
estimate `abs_integral_localStrainDifference_mul_le` adds the two half-lines, using that `k_A` is
even in `s₁`, and reduces negative heights to positive ones since `k_A` is odd in `s₂`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Lemma 3.1, p. 28, Lemma 3.6, p. 29,
  and Section 3.3, (3.16)-(3.24), pp. 31-36.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter PDE.Analysis.Rearrangement
open scoped ENNReal NNReal Topology

namespace IncompressibleFlow.SharpHolder

/-- The localized kernel
`k_A(s₁, s₂) = 1{|s₁ + 1/2| ≤ A} K₁(s₁ + 1/2, s₂) - 1{|s₁ - 1/2| ≤ A} K₁(s₁ - 1/2, s₂)` of
Chen and Hou, Part I, (3.16), on a line of height `s₂` inside the box. -/
def localStrainDifference (A s₁ s₂ : ℝ) : ℝ :=
  (if |s₁ + 1 / 2| ≤ A then strainDensity (s₁ + 1 / 2) s₂ else 0) -
    if |s₁ - 1 / 2| ≤ A then strainDensity (s₁ - 1 / 2) s₂ else 0

/-- The sign threshold `c = max(1/2, min(f(s₂), A - 1/2))` of the localized kernel on
`s₁ ≥ 0`; it is the threshold `s_c` of Chen and Hou, Part I, (3.18), in each of the cases
`A ∈ [1/2, 1]`, `A ∈ (1, f(s₂) + 1/2)` and `A ≥ f(s₂) + 1/2`. -/
def localStrainThreshold (A s₂ : ℝ) : ℝ :=
  max (1 / 2) (min (strainThreshold s₂) (A - 1 / 2))

/-- The transport cost `M(s₂) = ∫_{f(s₂)}^∞ |Δ(s₁, s₂)| |T(s₁, s₂) - s₁|^{1/2} ds₁` of the full
kernel on the line of height `s₂`, as an extended real. -/
def strainCost (s₂ : ℝ) : ℝ≥0∞ :=
  ∫⁻ s₁ in Ioi (strainThreshold s₂),
    ENNReal.ofReal (|strainDifference s₁ s₂| * |strainMap s₁ s₂ - s₁| ^ (1 / 2 : ℝ))

/-- The constant `C₁(b) = (4/π) ∫_0^b ∫_{f(s₂)}^∞ |T(s₁, s₂) - s₁|^{1/2} |Δ(s₁, s₂)| ds₁ ds₂` of
Chen and Hou, Part I, Lemma 3.1, as an extended real. Since `Δ ≤ 0` for `s₁ ≥ f(s₂)`, it equals
`(4/π) |∫∫ |T - s₁|^{1/2} Δ|` whenever that real integral exists. -/
def strainConstant (b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (4 / Real.pi) * ∫⁻ s₂ in Ioo 0 b, strainCost s₂

/-- `C₁` is nondecreasing. -/
theorem monotone_strainConstant : Monotone strainConstant := fun _ _ h ↦
  mul_le_mul_right (lintegral_mono_set (Ioo_subset_Ioo_right h)) _

/-- `C₁(b) = 0` for `b ≤ 0`. -/
theorem strainConstant_of_nonpos {b : ℝ} (hb : b ≤ 0) : strainConstant b = 0 := by
  rw [strainConstant, Ioo_eq_empty (not_lt.2 hb), Measure.restrict_empty, lintegral_zero_measure,
    mul_zero]

/-- The integrand of the transport cost is jointly measurable in `(s₂, s₁)`, including the moving
domain `s₁ > f(s₂)`. -/
theorem measurable_strainCost_integrand :
    Measurable fun v : ℝ × ℝ ↦ (Ioi (strainThreshold v.1)).indicator (fun s₁ ↦
      ENNReal.ofReal (|strainDifference s₁ v.1| * |strainMap s₁ v.1 - s₁| ^ (1 / 2 : ℝ))) v.2 := by
  have hf : Measurable fun v : ℝ × ℝ ↦ strainThreshold v.1 := by
    unfold strainThreshold
    fun_prop
  have hT : Measurable fun v : ℝ × ℝ ↦ strainMap v.2 v.1 := by
    have h := measurable_strainMap.comp measurable_swap
    simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap] using h
  have hΔ : Measurable fun v : ℝ × ℝ ↦ strainDifference v.2 v.1 := by
    unfold strainDifference
    simp only [strainDensity_eq]
    fun_prop
  refine Measurable.ite (measurableSet_lt hf measurable_snd) ?_ measurable_const
  exact ((continuous_abs.measurable.comp hΔ).mul
    ((continuous_abs.measurable.comp (hT.sub measurable_snd)).pow_const _)).ennreal_ofReal

/-- The transport cost `M` is measurable. -/
theorem measurable_strainCost : Measurable strainCost := by
  have h := measurable_strainCost_integrand.lintegral_prod_right' (ν := volume)
  have e : strainCost = fun s₂ ↦ ∫⁻ s₁, (Ioi (strainThreshold s₂)).indicator (fun s₁ ↦
      ENNReal.ofReal (|strainDifference s₁ s₂| * |strainMap s₁ s₂ - s₁| ^ (1 / 2 : ℝ))) s₁ := by
    funext s₂
    rw [strainCost, lintegral_indicator measurableSet_Ioi]
  rw [e]
  exact h

/-! ### The localized kernel -/

section Local

variable {A s₁ s₂ : ℝ}

/-- The localized kernel is even in `s₁`. -/
theorem localStrainDifference_neg_left (A s₁ s₂ : ℝ) :
    localStrainDifference A (-s₁) s₂ = localStrainDifference A s₁ s₂ := by
  simp only [localStrainDifference]
  rw [show -s₁ + 1 / 2 = -(s₁ - 1 / 2) by ring, show -s₁ - 1 / 2 = -(s₁ + 1 / 2) by ring,
    abs_neg, abs_neg, strainDensity_neg_left, strainDensity_neg_left]
  split_ifs <;> ring

/-- The localized kernel is odd in `s₂`. -/
theorem localStrainDifference_neg_right (A s₁ s₂ : ℝ) :
    localStrainDifference A s₁ (-s₂) = -localStrainDifference A s₁ s₂ := by
  simp only [localStrainDifference, strainDensity_neg_right]
  split_ifs <;> ring

/-- On `[0, A - 1/2]` the localized kernel is the full kernel. -/
theorem localStrainDifference_of_le (h₀ : 0 ≤ s₁) (h : s₁ ≤ A - 1 / 2) :
    localStrainDifference A s₁ s₂ = strainDifference s₁ s₂ := by
  have hA : 1 / 2 ≤ A := by linarith
  rw [localStrainDifference, ite_eq_left (abs_le.2 ⟨by linarith, by linarith⟩),
    ite_eq_left (abs_le.2 ⟨by linarith, by linarith⟩), strainDifference]

/-- On `(A - 1/2, A + 1/2]` only the right term of the localized kernel survives. -/
theorem localStrainDifference_of_lt (hA : 1 / 2 ≤ A) (h : A - 1 / 2 < s₁)
    (h' : s₁ ≤ A + 1 / 2) : localStrainDifference A s₁ s₂ = -strainDensity (s₁ - 1 / 2) s₂ := by
  rw [localStrainDifference, ite_eq_right (fun hle ↦ by linarith [(abs_le.1 hle).2]),
    ite_eq_left (abs_le.2 ⟨by linarith, by linarith⟩), zero_sub]

/-- The localized kernel vanishes for `|s₁| > A + 1/2`. -/
theorem localStrainDifference_eq_zero (h : A + 1 / 2 < |s₁|) :
    localStrainDifference A s₁ s₂ = 0 := by
  have h₁ : ¬|s₁ + 1 / 2| ≤ A := fun hle ↦ by
    rcases abs_le.1 hle with ⟨h₁, h₂⟩
    rcases le_abs'.1 h.le with h₃ | h₃ <;> [skip; skip] <;>
      cases abs_cases s₁ <;> linarith
  have h₂ : ¬|s₁ - 1 / 2| ≤ A := fun hle ↦ by
    rcases abs_le.1 hle with ⟨h₁, h₂⟩
    cases abs_cases s₁ <;> linarith
  rw [localStrainDifference, ite_eq_right h₁, ite_eq_right h₂, sub_zero]

/-- The localized kernel is measurable in `s₁`. -/
theorem measurable_localStrainDifference (A s₂ : ℝ) :
    Measurable fun s₁ ↦ localStrainDifference A s₁ s₂ := by
  unfold localStrainDifference
  simp only [strainDensity_eq]
  refine Measurable.sub (Measurable.ite ?_ (by fun_prop) measurable_const)
    (Measurable.ite ?_ (by fun_prop) measurable_const)
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact measurableSet_le (by fun_prop) measurable_const

/-- The localized kernel is bounded by `1 / s₂²`. -/
theorem abs_localStrainDifference_le (A s₁ : ℝ) {s₂ : ℝ} (h : s₂ ≠ 0) :
    |localStrainDifference A s₁ s₂| ≤ 1 / s₂ ^ 2 := by
  have hb : ∀ a, |strainDensity a s₂| ≤ 1 / (2 * s₂ ^ 2) := fun a ↦
    (abs_strainDensity_le a s₂).trans (one_div_le_one_div_of_le (by positivity)
      (by nlinarith [sq_nonneg a]))
  have hb' : ∀ (p : Prop) [Decidable p] (a : ℝ),
      |(if p then strainDensity a s₂ else 0)| ≤ 1 / (2 * s₂ ^ 2) := fun p _ a ↦ by
    split_ifs
    · exact hb a
    · simp only [abs_zero]
      positivity
  calc |localStrainDifference A s₁ s₂| ≤ 1 / (2 * s₂ ^ 2) + 1 / (2 * s₂ ^ 2) :=
        (abs_sub _ _).trans (add_le_add (hb' _ _) (hb' _ _))
    _ = 1 / s₂ ^ 2 := by field_simp; ring

/-- The localized kernel vanishes outside `[-(A + 1/2), A + 1/2]`. -/
theorem localStrainDifference_eq_indicator (A s₂ : ℝ) :
    (fun s₁ ↦ localStrainDifference A s₁ s₂) =
      (Icc (-(A + 1 / 2)) (A + 1 / 2)).indicator fun s₁ ↦ localStrainDifference A s₁ s₂ := by
  ext s₁
  by_cases h : s₁ ∈ Icc (-(A + 1 / 2)) (A + 1 / 2)
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h, localStrainDifference_eq_zero]
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h <;> cases abs_cases s₁ <;> linarith

/-- The localized kernel is integrable on the line for `s₂ ≠ 0`. -/
theorem integrable_localStrainDifference (A : ℝ) {s₂ : ℝ} (h : s₂ ≠ 0) :
    Integrable fun s₁ ↦ localStrainDifference A s₁ s₂ := by
  rw [localStrainDifference_eq_indicator]
  refine (integrableOn_const (C := 1 / s₂ ^ 2) (s := Icc (-(A + 1 / 2)) (A + 1 / 2))
    (by simp)).integrable_indicator measurableSet_Icc |>.mono'
    ((measurable_localStrainDifference A s₂).indicator measurableSet_Icc).aestronglyMeasurable
    (Eventually.of_forall fun s ↦ ?_)
  by_cases hs : s ∈ Icc (-(A + 1 / 2)) (A + 1 / 2)
  · rw [indicator_of_mem hs, indicator_of_mem hs, Real.norm_eq_abs]
    exact abs_localStrainDifference_le A s h
  · rw [indicator_of_notMem hs, indicator_of_notMem hs, norm_zero]

/-! ### Signs and mass on the half-line -/

/-- The localized threshold is at least `1/2`. -/
theorem one_half_le_localStrainThreshold : 1 / 2 ≤ localStrainThreshold A s₂ := le_max_left _ _

/-- The localized threshold is at most the threshold `f(s₂)`. -/
theorem localStrainThreshold_le_strainThreshold :
    localStrainThreshold A s₂ ≤ strainThreshold s₂ :=
  max_le (one_half_le_strainThreshold s₂) (min_le_left _ _)

/-- The localized threshold is at most `A + 1/2`. -/
theorem localStrainThreshold_le (hA : 1 / 2 ≤ A) : localStrainThreshold A s₂ ≤ A + 1 / 2 :=
  max_le (by linarith) ((min_le_right _ _).trans (by linarith))

variable (hA : 1 / 2 ≤ A) (hs₂ : 0 < s₂)
include hA hs₂

omit hA in
/-- `k_A ≥ 0` on `[0, c]`. For `A < 1/2` the threshold is `1/2` and only the right term can
survive. -/
theorem localStrainDifference_nonneg (h₀ : 0 ≤ s₁) (h : s₁ ≤ localStrainThreshold A s₂) :
    0 ≤ localStrainDifference A s₁ s₂ := by
  rcases lt_or_ge A (1 / 2) with hA | hA
  · have hc : localStrainThreshold A s₂ = 1 / 2 :=
      max_eq_left ((min_le_right _ _).trans (by linarith))
    rw [hc] at h
    rw [localStrainDifference, ite_eq_right (fun hle ↦ by linarith [(abs_le.1 hle).2])]
    split_ifs
    · rw [zero_sub, neg_nonneg, strainDensity_eq]
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hs₂.le)
        (by positivity)
    · simp
  have hcf := localStrainThreshold_le_strainThreshold (A := A) (s₂ := s₂)
  rcases le_or_gt s₁ (A - 1 / 2) with h' | h'
  · rw [localStrainDifference_of_le h₀ h']
    rcases eq_or_lt_of_le (h.trans hcf) with he | hlt
    · rw [he, strainDifference_eq hs₂.ne', strainQuartic_strainThreshold, mul_zero, zero_div]
    · exact ((strainDifference_pos_iff h₀ hs₂).2 hlt).le
  · -- here `c = 1/2`, so `s₁ ≤ 1/2`
    have hc : localStrainThreshold A s₂ = 1 / 2 := by
      unfold localStrainThreshold at h ⊢
      rcases le_total (min (strainThreshold s₂) (A - 1 / 2)) (1 / 2) with hm | hm
      · exact max_eq_left hm
      · rw [max_eq_right hm] at h
        linarith [min_le_right (strainThreshold s₂) (A - 1 / 2)]
    rw [localStrainDifference_of_lt hA h' (by linarith [localStrainThreshold_le (s₂ := s₂) hA]),
      neg_nonneg, strainDensity_eq]
    rw [hc] at h
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hs₂.le)
      (by positivity)

/-- `k_A < 0` on `(c, A + 1/2]`. -/
theorem localStrainDifference_neg (h : localStrainThreshold A s₂ < s₁) (h' : s₁ ≤ A + 1 / 2) :
    localStrainDifference A s₁ s₂ < 0 := by
  have hc := one_half_le_localStrainThreshold (A := A) (s₂ := s₂)
  rcases le_or_gt s₁ (A - 1 / 2) with h'' | h''
  · -- here `c = f`
    have hcf : localStrainThreshold A s₂ = strainThreshold s₂ := by
      have hmin : min (strainThreshold s₂) (A - 1 / 2) = strainThreshold s₂ := by
        refine min_eq_left (le_of_not_gt fun hlt ↦ ?_)
        have : localStrainThreshold A s₂ = max (1 / 2) (A - 1 / 2) := by
          rw [localStrainThreshold, min_eq_right hlt.le]
        rw [this] at h
        exact absurd h'' (not_le.2 (lt_of_le_of_lt (le_max_right _ _) h))
      rw [localStrainThreshold, hmin, max_eq_right (one_half_le_strainThreshold s₂)]
    rw [localStrainDifference_of_le (by linarith) h'']
    exact (strainDifference_neg_iff (by linarith) hs₂).2 (hcf ▸ h)
  · rw [localStrainDifference_of_lt hA h'' h', neg_lt_zero, strainDensity_eq]
    exact div_pos (mul_pos (by linarith) hs₂) (by positivity)

/-- `0 ≤ k_A ≤ Δ` fails only through the cut of the left kernel: `k_A ≤ Δ` on `[0, A + 1/2]`. -/
theorem localStrainDifference_le (h₀ : 0 ≤ s₁) (h : s₁ ≤ A + 1 / 2) :
    localStrainDifference A s₁ s₂ ≤ strainDifference s₁ s₂ := by
  rcases le_or_gt s₁ (A - 1 / 2) with h' | h'
  · rw [localStrainDifference_of_le h₀ h']
  · rw [localStrainDifference_of_lt hA h' h, strainDifference]
    have : 0 ≤ strainDensity (s₁ + 1 / 2) s₂ := by
      rw [strainDensity_eq]
      exact div_nonneg (mul_nonneg (by linarith) hs₂.le) (by positivity)
    linarith

/-- The localized kernel has zero mass on the half-line. -/
theorem integral_Ioi_localStrainDifference : ∫ s in Ioi 0, localStrainDifference A s s₂ = 0 := by
  -- split the kernel into its two terms on the half-line
  have e : EqOn (fun s ↦ localStrainDifference A s s₂)
      (fun s ↦ (Iic (A - 1 / 2)).indicator (fun s ↦ strainDensity (s + 1 / 2) s₂) s -
        (Iic (A + 1 / 2)).indicator (fun s ↦ strainDensity (s - 1 / 2) s₂) s) (Ioi 0) := by
    intro s hs
    have hs0 : 0 < s := hs
    simp only [localStrainDifference, indicator, mem_Iic]
    congr 1
    · exact if_congr ⟨fun h ↦ by linarith [(abs_le.1 h).2],
        fun h ↦ abs_le.2 ⟨by linarith, by linarith⟩⟩ rfl rfl
    · exact if_congr ⟨fun h ↦ by linarith [(abs_le.1 h).2],
        fun h ↦ abs_le.2 ⟨by linarith, by linarith⟩⟩ rfl rfl
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_sub]
  · rw [setIntegral_indicator measurableSet_Iic, setIntegral_indicator measurableSet_Iic,
      Ioi_inter_Iic, Ioi_inter_Iic, ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_add_right (fun s ↦ strainDensity s s₂),
      intervalIntegral.integral_comp_sub_right (fun s ↦ strainDensity s s₂),
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ ↦ hasDerivAt_strainPrimitive hs₂.ne' t)
        ((continuous_strainDensity_left hs₂.ne').intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ ↦ hasDerivAt_strainPrimitive hs₂.ne' t)
        ((continuous_strainDensity_left hs₂.ne').intervalIntegrable _ _)]
    simp only [strainPrimitive]
    ring_nf
  · exact (((integrable_strainDensity_left hs₂.ne').comp_add_right (1 / 2)).indicator
      measurableSet_Iic).integrableOn
  · exact (((integrable_strainDensity_left hs₂.ne').comp_sub_right (1 / 2)).indicator
      measurableSet_Iic).integrableOn

end Local

/-! ### The full kernel on the half-line -/

section Full

variable {s₂ : ℝ}

/-- The full kernel on the half-line with the sign convention of the transport lemma:
`-Δ(s, s₂)` for `s > 0` and `0` otherwise. -/
private def fullKernel (s₂ s : ℝ) : ℝ :=
  if 0 < s then -strainDifference s s₂ else 0

/-- The full kernel is `-Δ(·, s₂)` times the indicator of `s > 0`. -/
private theorem fullKernel_eq_indicator (s₂ : ℝ) :
    fullKernel s₂ = (Ioi 0).indicator fun s ↦ -strainDifference s s₂ := by
  ext s
  simp only [fullKernel, indicator, mem_Ioi]

variable (hs₂ : 0 < s₂)
include hs₂

/-- For `s₂ > 0` the full kernel is integrable. -/
private theorem integrable_fullKernel : Integrable (fullKernel s₂) := by
  rw [fullKernel_eq_indicator]
  exact (integrable_strainDifference_left hs₂.ne').neg.indicator measurableSet_Ioi

/-- For `s₂ > 0` the full kernel has zero mass. -/
private theorem integral_fullKernel : ∫ s, fullKernel s₂ s = 0 := by
  rw [fullKernel_eq_indicator, integral_indicator measurableSet_Ioi, integral_neg,
    integral_Ioi_strainDifference hs₂.ne', neg_zero]

/-- For `s₂ > 0` the full kernel is `≤ 0` below the threshold `f(s₂)`. -/
private theorem fullKernel_nonpos :
    ∀ᵐ x, x < strainThreshold s₂ → fullKernel s₂ x ≤ 0 :=
  Eventually.of_forall fun x hx ↦ by
    by_cases h0 : 0 < x
    · simp only [fullKernel, ite_eq_left h0]
      exact neg_nonpos.2 ((strainDifference_pos_iff h0.le hs₂).2 hx).le
    · simp [fullKernel, h0]

/-- For `s₂ > 0` the full kernel is `≥ 0` above the threshold `f(s₂)`. -/
private theorem fullKernel_nonneg :
    ∀ᵐ x, strainThreshold s₂ < x → 0 ≤ fullKernel s₂ x :=
  Eventually.of_forall fun x hx ↦ by
    have h0 : 0 < x := (strainThreshold_pos s₂).trans hx
    simp only [fullKernel, ite_eq_left h0]
    exact neg_nonneg.2 ((strainDifference_neg_iff h0.le hs₂).2 hx).le

/-- For `s₂ > 0` the full kernel is balanced at `f(s₂)` with weight exponent `0`. -/
private theorem isBalancedKernel_fullKernel :
    IsBalancedKernel (fullKernel s₂) (strainThreshold s₂) 0 :=
  isBalancedKernel_of_integral_eq_zero (integrable_fullKernel hs₂) (fullKernel_nonpos hs₂)
    (fullKernel_nonneg hs₂) (integral_fullKernel hs₂)
    ((integrable_fullKernel hs₂).congr (Eventually.of_forall fun x ↦ by simp))

/-- For `s₂ > 0` the map `T(·, s₂)` matches the masses of the full kernel on the two sides of
`f(s₂)`. -/
private theorem isMassMatching_fullKernel :
    IsMassMatching (fullKernel s₂) (strainThreshold s₂) fun s ↦ strainMap s s₂ := by
  refine isMassMatching_of_integral_eq_zero (integrable_fullKernel hs₂) (fullKernel_nonpos hs₂)
    (fullKernel_nonneg hs₂) (integral_fullKernel hs₂)
    (measurable_strainMap_left s₂).aemeasurable ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy _
    exact strainMap_lt_strainThreshold hs₂ hy
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy _
    have hy0 : 0 < y := (strainThreshold_pos s₂).trans hy
    have hT := strainMap_pos hy0 hs₂.ne'
    have e : EqOn (fullKernel s₂) (fun s ↦ -strainDifference s s₂) (uIcc (strainMap y s₂) y) := by
      intro s hs
      have : 0 < s := lt_of_lt_of_le (lt_min hT hy0) hs.1
      simp only [fullKernel, ite_eq_left this]
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_neg,
      integral_strainDifference hs₂.ne', strainPotential_strainMap hy0 hs₂.ne', sub_self,
      neg_zero]

/-- The transport cost of the full kernel computed on the left side:
`∫_0^{f} |Δ(x, s₂)| |T(x, s₂) - x|^{1/2} dx = M(s₂)`. -/
private theorem lintegral_fullKernel_left :
    ∫⁻ x in Iio (strainThreshold s₂), ‖fullKernel s₂ x‖ₑ *
      ENNReal.ofReal (|strainMap x s₂ - x| ^ (1 / 2 : ℝ)) = strainCost s₂ := by
  have hφ : Measurable fun x ↦ ENNReal.ofReal (|strainMap x s₂ - x| ^ (1 / 2 : ℝ)) :=
    ((continuous_abs.measurable.comp ((measurable_strainMap_left s₂).sub measurable_id)).pow_const
      _).ennreal_ofReal
  rw [(isBalancedKernel_fullKernel hs₂).lintegral_comp_eq (isMassMatching_fullKernel hs₂)
    hφ.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  have hy0 : 0 < y := (strainThreshold_pos s₂).trans hy
  simp only [fullKernel, ite_eq_left hy0, strainMap_strainMap hy0 hs₂.ne', enorm_neg,
    Real.enorm_eq_ofReal_abs]
  rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_sub_comm y]

end Full

/-! ### The half-line transport estimate -/

section HalfLine

variable {A s₂ : ℝ}

/-- The localized kernel on the half-line with the sign convention of the transport lemma. -/
private def halfKernel (A s₂ s : ℝ) : ℝ :=
  if 0 < s then -localStrainDifference A s s₂ else 0

/-- The localized kernel on the half-line is `-k_A(·, s₂)` times the indicator of `s > 0`. -/
private theorem halfKernel_eq_indicator (A s₂ : ℝ) :
    halfKernel A s₂ = (Ioi 0).indicator fun s ↦ -localStrainDifference A s s₂ := by
  ext s
  simp only [halfKernel, indicator, mem_Ioi]

variable (hA : 1 / 2 ≤ A) (hs₂ : 0 < s₂)
include hA hs₂

omit hA in
/-- For `s₂ > 0` the localized kernel on the half-line is integrable. -/
private theorem integrable_halfKernel : Integrable (halfKernel A s₂) := by
  rw [halfKernel_eq_indicator]
  exact (integrable_localStrainDifference A hs₂.ne').neg.indicator measurableSet_Ioi

/-- For `A ≥ 1/2` and `s₂ > 0` the localized kernel on the half-line has zero mass. -/
private theorem integral_halfKernel : ∫ s, halfKernel A s₂ s = 0 := by
  rw [halfKernel_eq_indicator, integral_indicator measurableSet_Ioi, integral_neg,
    integral_Ioi_localStrainDifference hA hs₂, neg_zero]

omit hA in
/-- The localized kernel on the half-line is `≤ 0` below the threshold `c`. -/
private theorem halfKernel_nonpos :
    ∀ᵐ x, x < localStrainThreshold A s₂ → halfKernel A s₂ x ≤ 0 :=
  Eventually.of_forall fun x hx ↦ by
    by_cases h0 : 0 < x
    · simp only [halfKernel, ite_eq_left h0]
      exact neg_nonpos.2 (localStrainDifference_nonneg hs₂ h0.le hx.le)
    · simp [halfKernel, h0]

omit hs₂ in
/-- The localized kernel on the half-line vanishes beyond `A + 1/2`. -/
private theorem halfKernel_eq_zero {x : ℝ} (hx : A + 1 / 2 < x) : halfKernel A s₂ x = 0 := by
  have h0 : 0 < x := by linarith
  simp only [halfKernel, ite_eq_left h0]
  rw [localStrainDifference_eq_zero (by rwa [abs_of_pos h0]), neg_zero]

/-- The localized kernel on the half-line is `≥ 0` above the threshold `c`. -/
private theorem halfKernel_nonneg :
    ∀ᵐ x, localStrainThreshold A s₂ < x → 0 ≤ halfKernel A s₂ x :=
  Eventually.of_forall fun x hx ↦ by
    rcases le_or_gt x (A + 1 / 2) with h | h
    · have h0 : 0 < x := lt_of_lt_of_le (by norm_num)
        ((one_half_le_localStrainThreshold (A := A) (s₂ := s₂)).trans hx.le)
      simp only [halfKernel, ite_eq_left h0]
      exact neg_nonneg.2 (localStrainDifference_neg hA hs₂ hx h).le
    · rw [halfKernel_eq_zero hA h]

omit hs₂ in
/-- The localized kernel on the half-line is supported in `[0, A + 1/2]`. -/
private theorem halfKernel_mem {x : ℝ} (hx : halfKernel A s₂ x ≠ 0) : x ∈ Icc 0 (A + 1 / 2) := by
  by_contra hmem
  apply hx
  rw [mem_Icc, not_and_or, not_le, not_le] at hmem
  rcases hmem with h | h
  · simp [halfKernel, not_lt.2 h.le]
  · exact halfKernel_eq_zero hA h

/-- `κ(x) |x - c|^{1/2}` is integrable for the localized kernel `κ` on the half-line. -/
private theorem integrable_halfKernel_mul_rpow :
    Integrable fun x ↦ halfKernel A s₂ x *
      |x - localStrainThreshold A s₂| ^ ((1 / 2 : ℝ≥0) : ℝ) := by
  set c := localStrainThreshold A s₂
  have hc0 : 0 ≤ c := le_trans (by norm_num) (one_half_le_localStrainThreshold (A := A) (s₂ := s₂))
  have h := (integrable_halfKernel (A := A) hs₂).mul_bdd
    (c := (A + 1 / 2 + c) ^ ((1 / 2 : ℝ≥0) : ℝ))
    (g := (Icc 0 (A + 1 / 2)).indicator fun x ↦ |x - c| ^ ((1 / 2 : ℝ≥0) : ℝ))
    ((((continuous_abs.comp (continuous_id.sub continuous_const)).rpow_const
      fun _ ↦ Or.inr (by positivity)).aestronglyMeasurable).indicator measurableSet_Icc)
    (Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ Icc 0 (A + 1 / 2)
      · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        refine Real.rpow_le_rpow (abs_nonneg _) ?_ (by positivity)
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2]
      · rw [indicator_of_notMem hx, norm_zero]
        positivity)
  refine h.congr (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ Icc 0 (A + 1 / 2)
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx, mul_zero]
    by_cases hk : halfKernel A s₂ x = 0
    · rw [hk, zero_mul]
    · exact absurd (halfKernel_mem hA hk) hx

/-- The localized kernel on the half-line is balanced at `c` with weight exponent `1/2`. -/
private theorem isBalancedKernel_halfKernel :
    IsBalancedKernel (halfKernel A s₂) (localStrainThreshold A s₂) (1 / 2) :=
  isBalancedKernel_of_integral_eq_zero (integrable_halfKernel (A := A) hs₂)
    (halfKernel_nonpos hs₂) (halfKernel_nonneg hA hs₂) (integral_halfKernel hA hs₂)
    (integrable_halfKernel_mul_rpow hA hs₂)

omit hA in
/-- The left mass of the localized kernel is its primitive: `∫_{t ≤ x} |κ| = ∫_0^x k_A` for
`0 ≤ x ≤ c`. -/
private theorem lintegral_Iic_halfKernel {x : ℝ} (hx₀ : 0 ≤ x)
    (hxc : x ≤ localStrainThreshold A s₂) :
    ∫⁻ t in Iic x, ‖halfKernel A s₂ t‖ₑ =
      ENNReal.ofReal (∫ s in (0 : ℝ)..x, localStrainDifference A s s₂) := by
  have hk := integrable_localStrainDifference A hs₂.ne'
  rw [intervalIntegral.integral_of_le hx₀, ofReal_integral_eq_lintegral_ofReal hk.integrableOn]
  · rw [halfKernel_eq_indicator]
    simp only [enorm_indicator_eq_indicator_enorm]
    rw [setLIntegral_indicator measurableSet_Ioi, Ioi_inter_Iic]
    refine setLIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    rw [enorm_neg, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (localStrainDifference_nonneg hs₂ ht.1.le (ht.2.trans hxc))]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact localStrainDifference_nonneg hs₂ ht.1.le (ht.2.trans hxc)

/-- The localized primitive vanishes at `A + 1/2`. -/
private theorem integral_localStrainDifference_end :
    ∫ s in (0 : ℝ)..(A + 1 / 2), localStrainDifference A s s₂ = 0 := by
  have hk := integrable_localStrainDifference A hs₂.ne'
  have hzero : ∫ s in Ioi (A + 1 / 2), localStrainDifference A s s₂ = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ ↦ (0 : ℝ)) fun s hs ↦
      localStrainDifference_eq_zero (by rw [abs_of_pos (by linarith [mem_Ioi.1 hs])]; exact hs)]
    simp
  have h0b : (0 : ℝ) ≤ A + 1 / 2 := by linarith
  have hsum := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hk.integrableOn (s := Ioc 0 (A + 1 / 2))) (hk.integrableOn (s := Ioi (A + 1 / 2)))
  rw [Ioc_union_Ioi_eq_Ioi h0b, integral_Ioi_localStrainDifference hA hs₂, hzero,
    add_zero] at hsum
  rw [intervalIntegral.integral_of_le h0b]
  exact hsum.symm

/-- The right mass of the localized kernel: `∫_{t ≥ y} |κ| = ∫_0^y k_A` for
`c ≤ y ≤ A + 1/2`. -/
private theorem lintegral_Ici_halfKernel {y : ℝ} (hyc : localStrainThreshold A s₂ ≤ y)
    (hyA : y ≤ A + 1 / 2) :
    ∫⁻ t in Ici y, ‖halfKernel A s₂ t‖ₑ =
      ENNReal.ofReal (∫ s in (0 : ℝ)..y, localStrainDifference A s s₂) := by
  have hk := integrable_localStrainDifference A hs₂.ne'
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num)
    ((one_half_le_localStrainThreshold (A := A) (s₂ := s₂)).trans hyc)
  have hsplit : ∫ s in (0 : ℝ)..y, localStrainDifference A s s₂ =
      ∫ s in Ioc y (A + 1 / 2), -localStrainDifference A s s₂ := by
    have h := intervalIntegral.integral_interval_sub_left (a := 0) (b := A + 1 / 2) (c := y)
      hk.intervalIntegrable hk.intervalIntegrable
    rw [integral_localStrainDifference_end hA hs₂, zero_sub] at h
    rw [integral_neg, ← intervalIntegral.integral_of_le hyA]
    linarith
  have hk' : IntegrableOn (fun s ↦ -localStrainDifference A s s₂) (Ioc y (A + 1 / 2)) :=
    hk.neg.integrableOn
  rw [hsplit, ofReal_integral_eq_lintegral_ofReal hk',
    setLIntegral_congr (Ioi_ae_eq_Ici (μ := volume) (a := y)).symm, halfKernel_eq_indicator]
  · simp only [enorm_indicator_eq_indicator_enorm]
    rw [setLIntegral_indicator measurableSet_Ioi, inter_eq_right.2 (Ioi_subset_Ioi hy0.le),
      ← Ioc_union_Ioi_eq_Ioi hyA, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl),
      setLIntegral_congr_fun measurableSet_Ioi (g := fun _ ↦ (0 : ℝ≥0∞)) fun t ht ↦ ?_,
      lintegral_zero, add_zero]
    · refine setLIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (neg_nonneg.2
        (localStrainDifference_neg hA hs₂ (hyc.trans_lt ht.1) ht.2).le)]
    · have h0 : A + 1 / 2 < |t| := by rw [abs_of_pos (by linarith [mem_Ioi.1 ht])]; exact ht
      rw [localStrainDifference_eq_zero h0, neg_zero, enorm_zero]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact neg_nonneg.2 (localStrainDifference_neg hA hs₂ (hyc.trans_lt ht.1) ht.2).le

/-- Strict positivity of the localized primitive inside `(c, A + 1/2)`. -/
private theorem integral_localStrainDifference_pos {y : ℝ} (hyc : localStrainThreshold A s₂ < y)
    (hyA : y < A + 1 / 2) : 0 < ∫ s in (0 : ℝ)..y, localStrainDifference A s s₂ := by
  have hk := integrable_localStrainDifference A hs₂.ne'
  have h := intervalIntegral.integral_interval_sub_left (a := 0) (b := A + 1 / 2) (c := y)
    hk.intervalIntegrable hk.intervalIntegrable
  rw [integral_localStrainDifference_end hA hs₂, zero_sub] at h
  have hpos : 0 < ∫ s in y..(A + 1 / 2), -localStrainDifference A s s₂ :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hk.neg.intervalIntegrable
      (fun s hs ↦ neg_pos.2 (localStrainDifference_neg hA hs₂ (hyc.trans hs.1) hs.2.le)) hyA
  rw [intervalIntegral.integral_neg] at hpos
  linarith

omit hA hs₂ in
/-- For `x ≤ 0` the localized kernel on the half-line has no mass on `(-∞, x]`. -/
private theorem lintegral_Iic_halfKernel_eq_zero {x : ℝ} (hx : x ≤ 0) :
    ∫⁻ t in Iic x, ‖halfKernel A s₂ t‖ₑ = 0 := by
  rw [setLIntegral_congr_fun measurableSet_Iic (g := fun _ ↦ (0 : ℝ≥0∞)) fun t ht ↦ ?_,
    lintegral_zero]
  simp [halfKernel, not_lt.2 ((mem_Iic.1 ht).trans hx)]

/-- The comparison of the localized and the full transport maps (Chen and Hou, Part I,
Section 3.3): if the localized kernel matches `x ∈ (0, c)` with `y ∈ (c, A + 1/2]`, that is
`∫_0^x k_A = ∫_0^y k_A`, then `y ≤ T(x)`. -/
private theorem le_strainMap_of_integral_eq {x y : ℝ} (hx : 0 < x)
    (hxc : x < localStrainThreshold A s₂) (hyA : y ≤ A + 1 / 2)
    (heq : ∫ s in (0 : ℝ)..x, localStrainDifference A s s₂ =
      ∫ s in (0 : ℝ)..y, localStrainDifference A s s₂) :
    y ≤ strainMap x s₂ := by
  have hk := integrable_localStrainDifference A hs₂.ne'
  have hcf := localStrainThreshold_le_strainThreshold (A := A) (s₂ := s₂)
  have hxf : x < strainThreshold s₂ := hxc.trans_le hcf
  have hTf := strainThreshold_lt_strainMap hx hs₂ hxf
  by_contra hlt
  push Not at hlt
  have hTA : strainMap x s₂ < A + 1 / 2 := hlt.trans_le hyA
  have h₁ : ∫ s in x..strainMap x s₂, localStrainDifference A s s₂ ≤ 0 := by
    have hxT : x ≤ strainMap x s₂ := (hxf.trans hTf).le
    calc ∫ s in x..strainMap x s₂, localStrainDifference A s s₂
        ≤ ∫ s in x..strainMap x s₂, strainDifference s s₂ :=
          intervalIntegral.integral_mono_on hxT hk.intervalIntegrable
            (integrable_strainDifference_left hs₂.ne').intervalIntegrable fun s hs ↦
              localStrainDifference_le hA hs₂ (hx.le.trans hs.1) (hs.2.trans hTA.le)
      _ = 0 := by
          rw [integral_strainDifference hs₂.ne', strainPotential_strainMap hx hs₂.ne', sub_self]
  have h₂ : ∫ s in strainMap x s₂..y, localStrainDifference A s s₂ < 0 := by
    have : 0 < ∫ s in strainMap x s₂..y, -localStrainDifference A s s₂ :=
      intervalIntegral.intervalIntegral_pos_of_pos_on hk.neg.intervalIntegrable
        (fun s hs ↦ neg_pos.2 (localStrainDifference_neg hA hs₂
          ((hcf.trans hTf.le).trans_lt hs.1) (hs.2.le.trans hyA))) hlt
    rw [intervalIntegral.integral_neg] at this
    linarith
  have h₃ := intervalIntegral.integral_interval_sub_left (a := 0) (b := y) (c := x)
    hk.intervalIntegrable hk.intervalIntegrable
  have h₄ := intervalIntegral.integral_add_adjacent_intervals (a := x) (b := strainMap x s₂)
    (c := y) hk.intervalIntegrable hk.intervalIntegrable
  linarith

/-- **The half-line transport estimate** of Chen and Hou, Part I, (3.18)-(3.24): for `s₂ > 0`,
`A ≥ 1/2` and `g` `1/2`-Hölder with constant `C` on `[0, A + 1/2]`,
`|∫_0^∞ k_A(s₁, s₂) g(s₁) ds₁| ≤ C M(s₂)`. -/
theorem abs_setIntegral_localStrainDifference_mul_le {g : ℝ → ℝ} {C : ℝ≥0}
    (hg : HolderOnWith C (1 / 2) g (Icc 0 (A + 1 / 2))) :
    ENNReal.ofReal |∫ s in Ioi 0, localStrainDifference A s s₂ * g s| ≤ C * strainCost s₂ := by
  have hbal := isBalancedKernel_halfKernel hA hs₂
  have hT := hbal.isMassMatching_transportMap
  have hS : MeasurableSet (Icc (0 : ℝ) (A + 1 / 2)) := measurableSet_Icc
  have hkS : ∀ᵐ x, halfKernel A s₂ x ≠ 0 → x ∈ Icc 0 (A + 1 / 2) :=
    Eventually.of_forall fun x hx ↦ halfKernel_mem hA hx
  have hc12 := one_half_le_localStrainThreshold (A := A) (s₂ := s₂)
  have hcf := localStrainThreshold_le_strainThreshold (A := A) (s₂ := s₂)
  have hcS : localStrainThreshold A s₂ ∈ Icc (0 : ℝ) (A + 1 / 2) :=
    ⟨by linarith, localStrainThreshold_le hA⟩
  have main := hbal.abs_integral_mul_sub_le hT (by norm_num) hS hkS hcS hg
  have h12 : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  rw [h12] at main
  -- the left side
  have hint := integrable_halfKernel (A := A) hs₂
  have hκg := integrable_mul_sub_of_holderOnWith (integrable_halfKernel_mul_rpow hA hs₂)
    (by norm_num) hS hkS hcS hg
  have hlhs : ∫ s in Ioi 0, localStrainDifference A s s₂ * g s =
      -∫ x, halfKernel A s₂ x * (g x - g (localStrainThreshold A s₂)) := by
    have h₁ : ∫ x, halfKernel A s₂ x * g x =
        (∫ x, halfKernel A s₂ x * (g x - g (localStrainThreshold A s₂))) +
          g (localStrainThreshold A s₂) * ∫ x, halfKernel A s₂ x := by
      rw [← integral_const_mul, ← integral_add hκg (hint.const_mul _)]
      congr 1
      ext x
      ring
    rw [integral_halfKernel hA hs₂, mul_zero, add_zero] at h₁
    rw [← h₁, halfKernel_eq_indicator, ← integral_neg, ← integral_indicator measurableSet_Ioi]
    congr 1 with x
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · simp only [indicator_of_mem hx]; ring
    · simp only [indicator_of_notMem hx, zero_mul, neg_zero]
  -- the cost
  set TA := transportMap (halfKernel A s₂) (localStrainThreshold A s₂)
  have hφ : Measurable fun x ↦ ENNReal.ofReal (|strainMap x s₂ - x| ^ (1 / 2 : ℝ)) :=
    ((continuous_abs.measurable.comp ((measurable_strainMap_left s₂).sub measurable_id)).pow_const
      _).ennreal_ofReal
  have hcostI := hbal.integrableOn_transportCost hT
  rw [h12] at hcostI
  have hcost : ENNReal.ofReal (∫ y in Ioi (localStrainThreshold A s₂),
      |halfKernel A s₂ y| * |y - TA y| ^ (1 / 2 : ℝ)) ≤
      strainCost s₂ := by
    rw [ofReal_integral_eq_lintegral_ofReal hcostI
      (Eventually.of_forall fun y ↦ by positivity)]
    calc ∫⁻ y in Ioi (localStrainThreshold A s₂),
          ENNReal.ofReal (|halfKernel A s₂ y| * |y - TA y| ^ (1 / 2 : ℝ))
        = ∫⁻ y in Ioi (localStrainThreshold A s₂),
            ‖halfKernel A s₂ y‖ₑ * ENNReal.ofReal (|y - TA y| ^ (1 / 2 : ℝ)) := by
          refine lintegral_congr fun y ↦ ?_
          rw [ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs]
      _ ≤ ∫⁻ y in Ioi (localStrainThreshold A s₂), ‖halfKernel A s₂ y‖ₑ *
            ENNReal.ofReal (|strainMap (TA y) s₂ - TA y| ^ (1 / 2 : ℝ)) := by
          refine lintegral_mono_ae ?_
          have hne : ∀ᵐ y ∂volume.restrict (Ioi (localStrainThreshold A s₂)), y ≠ A + 1 / 2 :=
            ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (measure_singleton (A + 1 / 2)))
          filter_upwards [hT.lt, hT.mass_eq, ae_restrict_mem measurableSet_Ioi, hne] with
            y hlt hmass hyc hyne
          by_cases hκy : halfKernel A s₂ y = 0
          · simp [hκy]
          have hyA : y ≤ A + 1 / 2 := (halfKernel_mem hA hκy).2
          have hxlt : TA y < localStrainThreshold A s₂ := hlt hκy
          have hm := hmass hκy
          rw [lintegral_Ici_halfKernel hA hs₂ (le_of_lt hyc) hyA] at hm
          have hpos := integral_localStrainDifference_pos hA hs₂ hyc (lt_of_le_of_ne hyA hyne)
          have hx0 : 0 < TA y := lt_of_not_ge fun hle ↦ not_le.2 hpos
            (ENNReal.ofReal_eq_zero.1 (by rw [← hm, lintegral_Iic_halfKernel_eq_zero hle]))
          rw [lintegral_Iic_halfKernel hs₂ hx0.le hxlt.le] at hm
          have hxnn : 0 ≤ ∫ s in (0 : ℝ)..TA y, localStrainDifference A s s₂ :=
            intervalIntegral.integral_nonneg hx0.le fun s hs ↦
              localStrainDifference_nonneg hs₂ hs.1 (hs.2.trans hxlt.le)
          have heq := (ENNReal.ofReal_eq_ofReal_iff hxnn hpos.le).1 hm
          have hle := le_strainMap_of_integral_eq hA hs₂ hx0 hxlt hyA heq
          have key : |y - TA y| ≤ |strainMap (TA y) s₂ - TA y| :=
            abs_le_abs (by linarith) (by linarith [mem_Ioi.1 hyc])
          exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow (abs_nonneg _) key (by norm_num))) _
      _ = ∫⁻ x in Iio (localStrainThreshold A s₂), ‖halfKernel A s₂ x‖ₑ *
            ENNReal.ofReal (|strainMap x s₂ - x| ^ (1 / 2 : ℝ)) :=
          (hbal.lintegral_comp_eq hT hφ.aemeasurable).symm
      _ ≤ ∫⁻ x in Iio (localStrainThreshold A s₂), ‖fullKernel s₂ x‖ₑ *
            ENNReal.ofReal (|strainMap x s₂ - x| ^ (1 / 2 : ℝ)) := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Iio).2
            (Eventually.of_forall fun x hx ↦ ?_))
          gcongr
          by_cases h0 : 0 < x
          · simp only [halfKernel, fullKernel, ite_eq_left h0, enorm_neg,
              Real.enorm_eq_ofReal_abs]
            have hx' : x ≤ localStrainThreshold A s₂ := (mem_Iio.1 hx).le
            refine ENNReal.ofReal_le_ofReal ?_
            rw [abs_of_nonneg (localStrainDifference_nonneg hs₂ h0.le hx'),
              abs_of_nonneg ((strainDifference_pos_iff h0.le hs₂).2
                ((mem_Iio.1 hx).trans_le hcf)).le]
            exact localStrainDifference_le hA hs₂ h0.le (hx'.trans hcS.2)
          · simp [halfKernel, h0]
      _ ≤ ∫⁻ x in Iio (strainThreshold s₂), ‖fullKernel s₂ x‖ₑ *
            ENNReal.ofReal (|strainMap x s₂ - x| ^ (1 / 2 : ℝ)) :=
          lintegral_mono_set (Iio_subset_Iio hcf)
      _ = strainCost s₂ := lintegral_fullKernel_left hs₂
  calc ENNReal.ofReal |∫ s in Ioi 0, localStrainDifference A s s₂ * g s|
      = ENNReal.ofReal |∫ x, halfKernel A s₂ x * (g x - g (localStrainThreshold A s₂))| := by
        rw [hlhs, abs_neg]
    _ ≤ ENNReal.ofReal (C * ∫ y in Ioi (localStrainThreshold A s₂),
          |halfKernel A s₂ y| * |y - TA y| ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_le_ofReal main
    _ = C * ENNReal.ofReal (∫ y in Ioi (localStrainThreshold A s₂),
          |halfKernel A s₂ y| * |y - TA y| ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ENNReal.ofReal_coe_nnreal]
    _ ≤ C * strainCost s₂ := by gcongr

end HalfLine

/-- **The line estimate** of Chen and Hou, Part I, Section 3.3: for `s₂ ≠ 0`, `A ≥ 1/2` and `g`
`1/2`-Hölder with constant `C` on `[-(A + 1/2), A + 1/2]`,
`|∫ k_A(s₁, s₂) g(s₁) ds₁| ≤ 2 C M(|s₂|)`. The two half-lines contribute `C M(|s₂|)` each, by the
evenness of `k_A` in `s₁`; negative heights reduce to positive ones by its oddness in `s₂`. -/
theorem abs_integral_localStrainDifference_mul_le {A s₂ : ℝ} (hA : 1 / 2 ≤ A) (hs₂ : s₂ ≠ 0)
    {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderOnWith C (1 / 2) g (Icc (-(A + 1 / 2)) (A + 1 / 2))) :
    ENNReal.ofReal |∫ s, localStrainDifference A s s₂ * g s| ≤ 2 * C * strainCost |s₂| := by
  -- reduce to a positive height
  have hred : |∫ s, localStrainDifference A s s₂ * g s| =
      |∫ s, localStrainDifference A s |s₂| * g s| := by
    rcases lt_or_gt_of_ne hs₂ with h | h
    · have e (s : ℝ) : localStrainDifference A s s₂ = -localStrainDifference A s (-s₂) := by
        rw [← localStrainDifference_neg_right, neg_neg]
      simp only [abs_of_neg h, e, neg_mul, integral_neg, abs_neg]
    · rw [abs_of_pos h]
  rw [hred]
  set σ := |s₂|
  have hσ : 0 < σ := abs_pos.2 hs₂
  set R := A + 1 / 2
  have hR : 0 ≤ R := by simp only [R]; linarith
  -- integrability of the product
  have hgc : ContinuousOn g (Icc (-R) R) := hg.continuousOn (by norm_num)
  have hint : Integrable fun s ↦ localStrainDifference A s σ * g s :=
    (integrableOn_iff_integrable_of_support_subset fun s hs ↦ by_contra fun hsR ↦ hs (by
      simp [localStrainDifference_eq_zero (not_le.1 fun h ↦ hsR (abs_le.1 h))])).1
      ((integrable_localStrainDifference A hσ.ne').integrableOn.mul_continuousOn hgc
        isCompact_Icc)
  -- the two half-lines
  have hsplit : ∫ s, localStrainDifference A s σ * g s =
      (∫ s in Ioi 0, localStrainDifference A s σ * g s) +
        ∫ s in Ioi 0, localStrainDifference A s σ * g (-s) := by
    rw [← integral_add_compl measurableSet_Ioi hint, compl_Ioi]
    congr 1
    simpa only [neg_zero, localStrainDifference_neg_left] using
      (integral_comp_neg_Ioi (0 : ℝ) fun s ↦ localStrainDifference A s σ * g s).symm
  have hg₁ : HolderOnWith C (1 / 2) g (Icc 0 R) :=
    hg.mono (Icc_subset_Icc (by linarith) le_rfl)
  have hg₂ : HolderOnWith C (1 / 2) (fun s ↦ g (-s)) (Icc 0 R) := fun x hx y hy ↦ by
    simpa only [edist_neg_neg] using hg (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩ (-y)
      ⟨by linarith [hy.2], by linarith [hy.1]⟩
  rw [hsplit]
  calc ENNReal.ofReal |(∫ s in Ioi 0, localStrainDifference A s σ * g s) +
        ∫ s in Ioi 0, localStrainDifference A s σ * g (-s)|
      ≤ ENNReal.ofReal |∫ s in Ioi 0, localStrainDifference A s σ * g s| +
          ENNReal.ofReal |∫ s in Ioi 0, localStrainDifference A s σ * g (-s)| :=
        (ENNReal.ofReal_le_ofReal (abs_add_le _ _)).trans ENNReal.ofReal_add_le
    _ ≤ C * strainCost σ + C * strainCost σ :=
        add_le_add (abs_setIntegral_localStrainDifference_mul_le hA hσ hg₁)
          (abs_setIntegral_localStrainDifference_mul_le hA hσ hg₂)
    _ = 2 * C * strainCost σ := by ring

end IncompressibleFlow.SharpHolder
