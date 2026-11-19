/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Primitive
public import PDE.Analysis.MeasureTheory.Lp.CommonSupportConvergence

/-!
# Compact convergence of L² primitives

Cauchy–Schwarz bounds the change in a primitive by the square root of
the interval length times the L² norm. This turns strong L² convergence
into uniform convergence of normalized primitives on bounded intervals.
Multiplication by a fixed continuous compactly supported function then
gives strong L² convergence on the whole real line. The primitives themselves
need not belong to L².
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology

namespace MeasureTheory

/-- Cauchy–Schwarz for the integral of an L² function over an ordered
bounded interval, using the L² norm on the whole real line. -/
theorem norm_intervalIntegral_le_sqrt_mul_norm {a b : ℝ} (hab : a ≤ b)
    (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ‖∫ x in a..b, f x‖ ≤ √(b - a) * ‖f‖ := by
  let χ : Lp ℝ 2 (volume : Measure ℝ) :=
    indicatorConstLp 2 (s := Ioc a b) measurableSet_Ioc
      (by simp only [Real.volume_Ioc, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]) 1
  have hχ : ‖χ‖ = √(b - a) := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [norm_one, Real.volume_real_Ioc, ENNReal.toReal_ofNat, one_mul]
    rw [max_eq_left (sub_nonneg.mpr hab), Real.sqrt_eq_rpow]
  have hinner : (∫ x in a..b, f x) = inner ℝ χ f := by
    rw [L2.inner_indicatorConstLp_one]
    exact intervalIntegral.integral_of_le hab
  rw [hinner, ← hχ]
  exact norm_inner_le_norm _ _

/-- The same primitive bound applies to either orientation of the interval. -/
theorem norm_intervalIntegral_le_sqrt_abs_mul_norm (a b : ℝ)
    (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ‖∫ x in a..b, f x‖ ≤ √|b - a| * ‖f‖ := by
  rcases le_total a b with hab | hba
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using
      norm_intervalIntegral_le_sqrt_mul_norm hab f
  · rw [intervalIntegral.integral_symm, norm_neg, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr hba)]
    exact norm_intervalIntegral_le_sqrt_mul_norm hba f

end MeasureTheory

namespace PDE.Analysis

/-- Normalized L² primitives commute with subtraction. -/
theorem l2Primitive_sub (f g : Lp ℝ 2 (volume : Measure ℝ)) (x : ℝ) :
    l2Primitive (f - g) x = l2Primitive f x - l2Primitive g x := by
  simp only [l2Primitive, intervalIntegral_eq_inner_indicator_sub, inner_sub_right]
  ring

/-- Strong L² convergence gives uniform convergence of the normalized
primitives on every set whose distance from the origin is bounded. -/
theorem tendstoUniformlyOn_l2Primitive_of_tendsto
    {ι : Type*} {l : Filter ι}
    {f : ι → Lp ℝ 2 (volume : Measure ℝ)} {g : Lp ℝ 2 (volume : Measure ℝ)}
    {s : Set ℝ} {R : ℝ} (hf : Tendsto f l (𝓝 g))
    (hR : ∀ x ∈ s, |x| ≤ R) :
    TendstoUniformlyOn (fun i ↦ l2Primitive (f i)) (l2Primitive g) l s := by
  have hlim : Tendsto (fun i ↦ √R * ‖f i - g‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      ((hf.sub (tendsto_const_nhds (x := g))).norm.const_mul (√R))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with i hi
  intro x hx
  rw [dist_comm, dist_eq_norm, ← l2Primitive_sub]
  calc
    ‖l2Primitive (f i - g) x‖ ≤ √|x| * ‖f i - g‖ := by
      simpa only [l2Primitive, sub_zero] using
        norm_intervalIntegral_le_sqrt_abs_mul_norm 0 x (f i - g)
    _ ≤ √R * ‖f i - g‖ :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hR x hx)) (norm_nonneg _)
    _ < ε := hi

/-- A continuous compactly supported multiplier makes every normalized L²
primitive square integrable, even when the primitive has a nonzero tail. -/
theorem memLp_l2Primitive_mul (f : Lp ℝ 2 (volume : Measure ℝ))
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    MemLp (fun x ↦ l2Primitive f x * φ x) 2 volume :=
  ((continuous_l2Primitive f).mul hφ).memLp_of_hasCompactSupport hcφ.mul_left

/-- Strong L² convergence of the integrands gives strong L² convergence of
their normalized primitives after multiplication by a continuous compactly
supported function. Square integrability of every product is derived. -/
theorem tendsto_toLp_l2Primitive_mul
    {ι : Type*} {l : Filter ι}
    {f : ι → Lp ℝ 2 (volume : Measure ℝ)} {g : Lp ℝ 2 (volume : Measure ℝ)}
    (hf : Tendsto f l (𝓝 g)) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Tendsto
      (fun i ↦ (memLp_l2Primitive_mul (f i) hφ hcφ).toLp
        (fun x ↦ l2Primitive (f i) x * φ x)) l
      (𝓝 ((memLp_l2Primitive_mul g hφ hcφ).toLp
        (fun x ↦ l2Primitive g x * φ x))) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
  have hsupp (u : Lp ℝ 2 (volume : Measure ℝ)) :
      Function.support (fun x ↦ l2Primitive u x * φ x) ⊆ tsupport φ :=
    (subset_tsupport _).trans tsupport_mul_subset_right
  apply tendsto_eLpNorm_sub_of_tendstoUniformlyOn (s := tsupport φ)
    (by norm_num) hcφ.isCompact.isClosed.measurableSet.nullMeasurableSet
    hcφ.isCompact.measure_ne_top
    (.of_forall fun i ↦ ((memLp_l2Primitive_mul (f i) hφ hcφ).sub
      (memLp_l2Primitive_mul g hφ hcφ)).aestronglyMeasurable)
    (.of_forall fun i ↦ hsupp (f i)) (hsupp g)
  obtain ⟨R, hR⟩ := hcφ.isCompact.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨M, hM⟩ := hcφ.isCompact.exists_bound_of_continuousOn hφ.continuousOn
  have hlim : Tendsto (fun i ↦ √R * ‖f i - g‖ * M) l (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero, zero_mul] using
      (((hf.sub (tendsto_const_nhds (x := g))).norm.const_mul (√R)).mul_const M)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with i hi
  intro x hx
  rw [dist_comm, dist_eq_norm, ← sub_mul, ← l2Primitive_sub, norm_mul]
  have hprimitive : ‖l2Primitive (f i - g) x‖ ≤ √R * ‖f i - g‖ := by
    calc
      ‖l2Primitive (f i - g) x‖ ≤ √|x| * ‖f i - g‖ := by
        simpa only [l2Primitive, sub_zero] using
          norm_intervalIntegral_le_sqrt_abs_mul_norm 0 x (f i - g)
      _ ≤ √R * ‖f i - g‖ :=
        mul_le_mul_of_nonneg_right
          (Real.sqrt_le_sqrt (by simpa only [Real.norm_eq_abs, id_eq] using hR x hx))
          (norm_nonneg _)
  calc
    ‖l2Primitive (f i - g) x‖ * ‖φ x‖ ≤ √R * ‖f i - g‖ * ‖φ x‖ :=
      mul_le_mul_of_nonneg_right hprimitive (norm_nonneg _)
    _ ≤ √R * ‖f i - g‖ * M :=
      mul_le_mul_of_nonneg_left (hM x hx) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    _ < ε := hi

end PDE.Analysis
