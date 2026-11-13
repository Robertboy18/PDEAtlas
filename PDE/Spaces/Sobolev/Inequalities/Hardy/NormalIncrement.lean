/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Inequalities.Hardy.Lp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Banach-valued Hardy control of a normal increment

For arbitrary real Banach-valued data, subtracting the boundary value gives Hardy control
of the normal increment with constant
`(p / (p - 1)) ^ p`. For compactly supported C¹ data, the increment has a constant tail;
the weight `t ^ (-p)` makes this tail integrable when `p > 1`.
-/

@[expose] public section

namespace SobolevSpace.Hardy

open Set MeasureTheory Filter
open scoped ENNReal Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The interval Hardy estimate after subtracting the left endpoint value. -/
theorem lintegral_normal_increment_window_le
    {u : ℝ → F} {a b p : ℝ} (ha : 0 < a) (hab : a < b)
    (hp : 1 < p) (hu : ContDiff ℝ 1 u)
    (hderiv : IntegrableOn (fun x ↦ ‖deriv u x‖ ^ p) (Ioi (0 : ℝ))) :
    (∫⁻ x in Ioc a b, ENNReal.ofReal (‖u x - u a‖ ^ p * x ^ (-p))) ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p *
        ∫ x in Ioi (0 : ℝ), ‖deriv u x‖ ^ p) := by
  have hp0 : 0 ≤ p := (zero_lt_one.trans hp).le
  have hcontinuous :
      ContinuousOn (fun x ↦ ‖u x - u a‖ ^ p * x ^ (-p)) (Icc a b) :=
    ((hu.continuous.sub continuous_const).norm.rpow_const
      (fun _ ↦ Or.inr hp0)).continuousOn.mul
        (continuousOn_id.rpow_const (fun x hx ↦ Or.inl (ha.trans_le hx.1).ne'))
  have hint : IntegrableOn (fun x ↦ ‖u x - u a‖ ^ p * x ^ (-p)) (Ioc a b) :=
    hcontinuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioc a b)] fun x ↦ ‖u x - u a‖ ^ p * x ^ (-p) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (ha.trans hx.1).le _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  apply ENNReal.ofReal_le_ofReal
  -- The scalar primitive is C¹ even when the norm on F is not smooth.
  let v : ℝ → ℝ := fun x ↦ ∫ t in a..x, ‖deriv u t‖
  have hdu : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
  have hv' (x : ℝ) : HasDerivAt v ‖deriv u x‖ x :=
    intervalIntegral.integral_hasDerivAt_right (hdu.norm.intervalIntegrable a x)
      hdu.norm.aestronglyMeasurable.stronglyMeasurableAtFilter hdu.norm.continuousAt
  have hderiv_v : deriv v = fun x ↦ ‖deriv u x‖ := funext fun x ↦ (hv' x).deriv
  have hv : ContDiff ℝ 1 v := contDiff_one_iff_deriv.mpr
    ⟨fun x ↦ (hv' x).differentiableAt, by simpa only [hderiv_v] using hdu.norm⟩
  have hmajorant (x : ℝ) (hax : a ≤ x) : ‖u x - u a‖ ≤ |v x| := by
    calc
      ‖u x - u a‖ = ‖∫ t in a..x, deriv u t‖ := by
        rw [intervalIntegral.integral_deriv_eq_sub
          (fun t _ ↦ hu.differentiable (by norm_num) t) (hdu.intervalIntegrable a x)]
      _ ≤ v x := intervalIntegral.norm_integral_le_integral_norm hax
      _ ≤ |v x| := le_abs_self _
  have hvcontinuous :
      ContinuousOn (fun x ↦ |v x| ^ p * x ^ (-p)) (Icc a b) :=
    (hv.continuous.abs.rpow_const (fun _ ↦ Or.inr hp0)).continuousOn.mul
      (continuousOn_id.rpow_const (fun x hx ↦ Or.inl (ha.trans_le hx.1).ne'))
  have hcompare := intervalIntegral.integral_mono_on (μ := volume) hab.le
    (hcontinuous.intervalIntegrable_of_Icc hab.le)
    (hvcontinuous.intervalIntegrable_of_Icc hab.le) (fun x hx ↦
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (norm_nonneg _) (hmajorant x hx.1) hp0)
        (Real.rpow_nonneg (ha.trans_le hx.1).le _))
  have hhardy := hardy_interval_lp (u := v) ha hab hp hv (by simp [v])
  simp only [hderiv_v, abs_norm] at hhardy
  rw [← intervalIntegral.integral_of_le hab.le]
  refine hcompare.trans (hhardy.trans (mul_le_mul_of_nonneg_left ?_ (by positivity)))
  rw [intervalIntegral.integral_of_le hab.le]
  exact setIntegral_mono_set hderiv
    (ae_of_all _ fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
    (ae_of_all _ fun x hx ↦ ha.trans hx.1)

/-- Hardy's estimate for the increment from zero, stated as a finite nonnegative integral.
The increment itself need not have compact support. -/
theorem lintegral_normal_increment_le
    {u : ℝ → F} {p : ℝ} (hp : 1 < p) (hu : ContDiff ℝ 1 u)
    (hcompact : HasCompactSupport u) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (‖u x - u 0‖ ^ p * x ^ (-p))) ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p *
        ∫ x in Ioi (0 : ℝ), ‖deriv u x‖ ^ p) := by
  have hp0 : 0 ≤ p := (zero_lt_one.trans hp).le
  have hderiv : IntegrableOn (fun x ↦ ‖deriv u x‖ ^ p) (Ioi (0 : ℝ)) :=
    ((hu.continuous_deriv (by norm_num)).norm.rpow_const
      (fun _ ↦ Or.inr hp0)).integrable_of_hasCompactSupport
        (hcompact.deriv.norm.rpow_const (zero_lt_one.trans hp).ne') |>.integrableOn
  let a (N : ℕ) : ℝ := 1 / ((N : ℝ) + 1)
  let b (N : ℕ) : ℝ := (N : ℝ) + 2
  let f (N : ℕ) : ℝ → ℝ≥0∞ :=
    (Ioc (a N) (b N)).indicator
      (fun x ↦ ENNReal.ofReal (‖u x - u (a N)‖ ^ p * x ^ (-p)))
  have ha (N : ℕ) : 0 < a N := by dsimp [a]; positivity
  have hab (N : ℕ) : a N < b N := by
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have ha1 : a N ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    dsimp [b]
    linarith
  have hmeas (N : ℕ) : Measurable (f N) :=
    (ENNReal.measurable_ofReal.comp
      ((((hu.continuous.sub continuous_const).norm.rpow_const
        (fun _ ↦ Or.inr hp0)).measurable).mul
        (measurable_id.pow_const (-p)))).indicator measurableSet_Ioc
  have hbound (N : ℕ) :
      (∫⁻ x, f N x) ≤ ENNReal.ofReal ((p / (p - 1)) ^ p *
        ∫ x in Ioi (0 : ℝ), ‖deriv u x‖ ^ p) := by
    rw [show f N = (Ioc (a N) (b N)).indicator
      (fun x ↦ ENNReal.ofReal (‖u x - u (a N)‖ ^ p * x ^ (-p))) from rfl,
      lintegral_indicator measurableSet_Ioc]
    exact lintegral_normal_increment_window_le (ha N) (hab N) hp hu hderiv
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hu0 : Tendsto (fun N ↦ u (a N)) atTop (𝓝 (u 0)) :=
    hu.continuous.continuousAt.tendsto.comp ha0
  have hlimit (x : ℝ) :
      Tendsto (fun N ↦ f N x) atTop
        (𝓝 ((Ioi (0 : ℝ)).indicator
          (fun x ↦ ENNReal.ofReal (‖u x - u 0‖ ^ p * x ^ (-p))) x)) := by
    by_cases hx : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
      have hlow : ∀ᶠ N in atTop, a N < x := ha0.eventually (gt_mem_nhds hx)
      have hhigh : ∀ᶠ N in atTop, x ≤ b N := by
        filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
          (eventually_ge_atTop (x - 2))] with N hN
        dsimp [b]
        linarith
      have hraw :
          Tendsto (fun N ↦ ENNReal.ofReal (‖u x - u (a N)‖ ^ p * x ^ (-p)))
            atTop (𝓝 (ENNReal.ofReal (‖u x - u 0‖ ^ p * x ^ (-p)))) :=
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          ((((tendsto_const_nhds.sub hu0).norm).rpow_const (Or.inr hp0)).mul_const _)
      apply hraw.congr'
      filter_upwards [hlow, hhigh] with N hN hN'
      simp only [f, indicator_of_mem (show x ∈ Ioc (a N) (b N) from ⟨hN, hN'⟩)]
    · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
      have hz (N : ℕ) : f N x = 0 :=
        indicator_of_notMem (fun h ↦ hx ((ha N).trans h.1)) _
      simpa only [hz] using (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
  calc
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (‖u x - u 0‖ ^ p * x ^ (-p))) =
        ∫⁻ x, liminf (fun N ↦ f N x) atTop := by
      rw [← lintegral_indicator measurableSet_Ioi]
      exact lintegral_congr (fun x ↦ (hlimit x).liminf_eq.symm)
    _ ≤ liminf (fun N ↦ ∫⁻ x, f N x) atTop := lintegral_liminf_le hmeas
    _ ≤ ENNReal.ofReal ((p / (p - 1)) ^ p *
        ∫ x in Ioi (0 : ℝ), ‖deriv u x‖ ^ p) :=
      liminf_le_of_frequently_le' (Eventually.of_forall hbound).frequently

omit [CompleteSpace F] in
/-- The weighted normal increment is integrable, including near zero and at infinity. The space
`F` need not be complete: the Hardy bound in its completion has the same integrand. -/
theorem integrableOn_normal_increment
    {u : ℝ → F} {p : ℝ} (hp : 1 < p) (hu : ContDiff ℝ 1 u)
    (hcompact : HasCompactSupport u) :
    IntegrableOn (fun x ↦ ‖u x - u 0‖ ^ p * x ^ (-p)) (Ioi (0 : ℝ)) := by
  let L : F →ₗᵢ[ℝ] UniformSpace.Completion F := UniformSpace.Completion.toComplₗᵢ
  have hle := lintegral_normal_increment_le (u := fun x ↦ L (u x)) hp (L.contDiff.comp hu)
    (hcompact.comp_left (map_zero L))
  simp only [← map_sub, LinearIsometry.norm_map] at hle
  have hmeas : Measurable (fun x ↦ ‖u x - u 0‖ ^ p * x ^ (-p)) :=
    (((hu.continuous.sub continuous_const).norm.rpow_const
      (fun _ ↦ Or.inr (zero_lt_one.trans hp).le)).measurable).mul
        (measurable_id.pow_const (-p))
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun x ↦ ‖u x - u 0‖ ^ p * x ^ (-p) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hx.le _)
  exact (lintegral_ofReal_ne_top_iff_integrable
    hmeas.aestronglyMeasurable hnonneg).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)

/-- Hardy control of the normal increment, in real-integral form. -/
theorem integral_normal_increment_le
    {u : ℝ → F} {p : ℝ} (hp : 1 < p) (hu : ContDiff ℝ 1 u)
    (hcompact : HasCompactSupport u) :
    (∫ x in Ioi (0 : ℝ), ‖u x - u 0‖ ^ p * x ^ (-p)) ≤
      (p / (p - 1)) ^ p * ∫ x in Ioi (0 : ℝ), ‖deriv u x‖ ^ p := by
  have hint := integrableOn_normal_increment hp hu hcompact
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun x ↦ ‖u x - u 0‖ ^ p * x ^ (-p) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hx.le _)
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (lintegral_normal_increment_le hp hu hcompact)
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg hint.aestronglyMeasurable,
    ENNReal.toReal_ofReal
      (mul_nonneg (by positivity) (integral_nonneg fun x ↦
        Real.rpow_nonneg (norm_nonneg _) _))] at h
  exact h

end SobolevSpace.Hardy
