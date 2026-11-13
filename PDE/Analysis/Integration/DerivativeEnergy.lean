/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import PDE.Analysis.MeasureTheory.Lp.Continuous
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import CAS.IntegrationTactic

/-!
# Interval estimates from derivative energy

For an arbitrary real function, square-integrable derivatives control endpoint
increments and midpoint remainders. Interior differentiability suffices for the
midpoint estimate, so the derivative may be singular at either endpoint.
An affine model uses the energy of `deriv g - r`, retaining cancellation with
any chosen slope `r`. Splitting at the midpoint gives the factor `(b - a)² / 8`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis

/-- Cauchy–Schwarz bounds a displacement by the interval's derivative energy. -/
theorem sub_sq_le_length_mul_integral_deriv_sq {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn g (Icc a b))
    (hd : DifferentiableOn ℝ g (Ioo a b))
    (he : MemLp (deriv g) 2 (volume.restrict (Ioc a b))) :
    (g b - g a) ^ 2 ≤ (b - a) * ∫ x in a..b, deriv g x ^ 2 := by
  have hi : IntervalIntegrable (fun x ↦ |deriv g x|) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (he.integrable (by norm_num)).abs
  have hdistance := norm_sub_le_integral_of_norm_deriv_le_of_le hab hc hd
    (Filter.Eventually.of_forall fun _ _ ↦ le_rfl) hi
  have hone : MemLp (fun _ : ℝ ↦ (1 : ℝ)) 2 (volume.restrict (Ioc a b)) :=
    memLp_const 1
  have hcs := integral_abs_mul_le_sqrt_integral_sq he hone
  simp only [mul_one, one_pow] at hcs
  rw [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul, mul_one] at hcs
  simp only [Real.norm_eq_abs, intervalIntegral.integral_of_le hab] at hdistance
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (hdistance.trans hcs)
  rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
    Real.sq_sqrt (sub_nonneg.mpr hab)] at hs
  simpa only [intervalIntegral.integral_of_le hab, mul_comm] using hs

/-- Anchoring at the right endpoint costs half the squared interval length.
No regularity at the left endpoint is needed. -/
theorem integral_sub_right_sq_le_deriv_energy {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hd : ∀ x ∈ Ioc a b, DifferentiableAt ℝ g x)
    (hg : MemLp g 2 (volume.restrict (Ioc a b)))
    (he : MemLp (deriv g) 2 (volume.restrict (Ioc a b))) :
    (∫ x in a..b, (g x - g b) ^ 2) ≤
      (b - a) ^ 2 / 2 * ∫ x in a..b, deriv g x ^ 2 := by
  let E := ∫ x in a..b, deriv g x ^ 2
  have heI : IntervalIntegrable (fun x ↦ deriv g x ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 he.integrable_sq
  have hgI : IntervalIntegrable (fun x ↦ (g x - g b) ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      ((hg.sub (memLp_const (g b))).integrable_sq)
  have hmajor : IntervalIntegrable (fun x ↦ (b - x) * E) volume a b :=
    (by fun_prop : Continuous (fun x : ℝ ↦ (b - x) * E)).intervalIntegrable _ _
  have hbound := intervalIntegral.integral_mono_on_of_le_Ioo hab hgI hmajor
    (fun x hx ↦ show (g x - g b) ^ 2 ≤ (b - x) * E from by
      have hsubset : Ioc x b ⊆ Ioc a b := Ioc_subset_Ioc hx.1.le le_rfl
      have hxe := he.mono_measure (Measure.restrict_mono hsubset le_rfl)
      have hsub := sub_sq_le_length_mul_integral_deriv_sq hx.2.le
        (fun y hy ↦ (hd y ⟨hx.1.trans_le hy.1, hy.2⟩).continuousAt.continuousWithinAt)
        (fun y hy ↦ (hd y ⟨hx.1.trans hy.1, hy.2.le⟩).differentiableWithinAt) hxe
      have hem := intervalIntegral.integral_mono_interval hx.1.le hx.2.le le_rfl
        (Filter.Eventually.of_forall fun y ↦ sq_nonneg (deriv g y)) heI
      rw [sub_sq_comm] at hsub
      exact hsub.trans (mul_le_mul_of_nonneg_left hem (sub_nonneg.mpr hx.2.le)))
  have hcalc : (∫ x in a..b, (b - x) * E) = (b - a) ^ 2 / 2 * E := by
    cas
  exact hbound.trans_eq hcalc

/-- Anchoring at the left endpoint allows a singular derivative at the right endpoint. -/
theorem integral_sub_left_sq_le_deriv_energy {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hd : ∀ x ∈ Ico a b, DifferentiableAt ℝ g x)
    (hg : MemLp g 2 (volume.restrict (Ioc a b)))
    (he : MemLp (deriv g) 2 (volume.restrict (Ioc a b))) :
    (∫ x in a..b, (g x - g a) ^ 2) ≤
      (b - a) ^ 2 / 2 * ∫ x in a..b, deriv g x ^ 2 := by
  let E := ∫ x in a..b, deriv g x ^ 2
  have heI : IntervalIntegrable (fun x ↦ deriv g x ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 he.integrable_sq
  have hgI : IntervalIntegrable (fun x ↦ (g x - g a) ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      ((hg.sub (memLp_const (g a))).integrable_sq)
  have hmajor : IntervalIntegrable (fun x ↦ (x - a) * E) volume a b :=
    (by fun_prop : Continuous (fun x : ℝ ↦ (x - a) * E)).intervalIntegrable _ _
  have hbound := intervalIntegral.integral_mono_on_of_le_Ioo hab hgI hmajor
    (fun x hx ↦ show (g x - g a) ^ 2 ≤ (x - a) * E from by
      have hsubset : Ioc a x ⊆ Ioc a b := Ioc_subset_Ioc le_rfl hx.2.le
      have hxe := he.mono_measure (Measure.restrict_mono hsubset le_rfl)
      have hsub := sub_sq_le_length_mul_integral_deriv_sq hx.1.le
        (fun y hy ↦ (hd y ⟨hy.1, hy.2.trans_lt hx.2⟩).continuousAt.continuousWithinAt)
        (fun y hy ↦ (hd y ⟨hy.1.le, hy.2.trans hx.2⟩).differentiableWithinAt) hxe
      have hem := intervalIntegral.integral_mono_interval le_rfl hx.1.le hx.2.le
        (Filter.Eventually.of_forall fun y ↦ sq_nonneg (deriv g y)) heI
      exact hsub.trans (mul_le_mul_of_nonneg_left hem (sub_nonneg.mpr hx.1.le)))
  have hcalc : (∫ x in a..b, (x - a) * E) = (b - a) ^ 2 / 2 * E := by
    cas
  exact hbound.trans_eq hcalc

/-- Integrating the distance separately on each half gives the factor `h²/8`.
Only interior differentiability and square integrability are required. -/
theorem integral_sub_midpoint_sq_le_deriv_energy {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x)
    (hg : MemLp g 2 (volume.restrict (Ioc a b)))
    (he : MemLp (deriv g) 2 (volume.restrict (Ioc a b))) :
    (∫ x in a..b, (g x - g ((a + b) / 2)) ^ 2) ≤
      (b - a) ^ 2 / 8 * ∫ x in a..b, deriv g x ^ 2 := by
  let m := (a + b) / 2
  have ham : a < m := by dsimp only [m]; linarith
  have hmb : m < b := by dsimp only [m]; linarith
  have hleft : volume.restrict (Ioc a m) ≤ volume.restrict (Ioc a b) :=
    Measure.restrict_mono (Ioc_subset_Ioc le_rfl hmb.le) le_rfl
  have hright : volume.restrict (Ioc m b) ≤ volume.restrict (Ioc a b) :=
    Measure.restrict_mono (Ioc_subset_Ioc ham.le le_rfl) le_rfl
  have hl := integral_sub_right_sq_le_deriv_energy ham.le
    (fun x hx ↦ hd x ⟨hx.1, hx.2.trans_lt hmb⟩)
    (hg.mono_measure hleft) (he.mono_measure hleft)
  have hr := integral_sub_left_sq_le_deriv_energy hmb.le
    (fun x hx ↦ hd x ⟨ham.trans_le hx.1, hx.2⟩)
    (hg.mono_measure hright) (he.mono_measure hright)
  have hgI : IntervalIntegrable (fun x ↦ (g x - g m) ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      ((hg.sub (memLp_const (g m))).integrable_sq)
  have heI : IntervalIntegrable (fun x ↦ deriv g x ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 he.integrable_sq
  have hleftSet : uIcc a m ⊆ uIcc a b := by
    rw [uIcc_of_le ham.le, uIcc_of_le hab.le]
    exact Icc_subset_Icc le_rfl hmb.le
  have hrightSet : uIcc m b ⊆ uIcc a b := by
    rw [uIcc_of_le hmb.le, uIcc_of_le hab.le]
    exact Icc_subset_Icc ham.le le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hgI.mono_set hleftSet) (hgI.mono_set hrightSet)]
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (heI.mono_set hleftSet) (heI.mono_set hrightSet)
  have hal : (m - a) ^ 2 / 2 = (b - a) ^ 2 / 8 := by dsimp only [m]; cas
  have har : (b - m) ^ 2 / 2 = (b - a) ^ 2 / 8 := by dsimp only [m]; cas
  rw [hal] at hl
  rw [har] at hr
  exact (add_le_add hl hr).trans_eq (by rw [← mul_add, hsum])

/-- An affine midpoint model retains its exact square integral. The remainder
uses the energy of the derivative minus the model slope, preserving cancellation. -/
theorem integral_sq_le_midpoint_affine_deriv_energy {g : ℝ → ℝ} {a b r η : ℝ}
    (hab : a < b) (hη : 0 < η)
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x)
    (hg : MemLp g 2 (volume.restrict (Ioc a b)))
    (he : MemLp (deriv g) 2 (volume.restrict (Ioc a b))) :
    (∫ x in a..b, g x ^ 2) ≤
      (1 + η) * ((b - a) * g ((a + b) / 2) ^ 2 + (b - a) ^ 3 / 12 * r ^ 2) +
        (1 + 1 / η) * (b - a) ^ 2 / 8 *
          ∫ x in a..b, (deriv g x - r) ^ 2 := by
  let m := (a + b) / 2
  let p (x : ℝ) := g m + r * (x - m)
  let e (x : ℝ) := g x - p x
  have hpc : Continuous p := by dsimp only [p]; fun_prop
  have hp : MemLp p 2 (volume.restrict (Ioc a b)) :=
    hpc.continuousOn.memLp_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  have hpd (x : ℝ) : HasDerivAt p r x := by dsimp only [p]; cas
  have hed (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt e (deriv g x - r) x :=
    (hd x hx).hasDerivAt.sub (hpd x)
  have heq : deriv e =ᵐ[volume.restrict (Ioc a b)] (fun x ↦ deriv g x - r) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hed x hx).deriv
  have hem : MemLp (deriv e) 2 (volume.restrict (Ioc a b)) :=
    (memLp_congr_ae heq).2 (he.sub (memLp_const r))
  have hr := integral_sub_midpoint_sq_le_deriv_energy hab
    (fun x hx ↦ (hed x hx).differentiableAt) (hg.sub hp) hem
  have hemid : e m = 0 := by simp only [e, p, sub_self, mul_zero, add_zero]
  change (∫ x in a..b, (e x - e m) ^ 2) ≤ _ at hr
  simp only [hemid, sub_zero] at hr
  have heIntegral : (∫ x in a..b, deriv e x ^ 2) =
      ∫ x in a..b, (deriv g x - r) ^ 2 := by
    simp only [intervalIntegral.integral_of_le hab.le]
    exact integral_congr_ae (heq.fun_comp fun t : ℝ ↦ t ^ 2)
  rw [heIntegral] at hr
  have hgI : IntervalIntegrable (fun x ↦ g x ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 hg.integrable_sq
  have hpI : IntervalIntegrable (fun x ↦ p x ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 hp.integrable_sq
  have heI : IntervalIntegrable (fun x ↦ e x ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 (hg.sub hp).integrable_sq
  have hmajor := (hpI.const_mul (1 + η)).add (heI.const_mul (1 + 1 / η))
  have hbound := intervalIntegral.integral_mono_on hab.le hgI hmajor (fun x _ ↦ by
    have hnonneg := div_nonneg (sq_nonneg (η * p x - e x)) hη.le
    have halg (u v : ℝ) : (η * u - v) ^ 2 / η =
        (1 + η) * u ^ 2 + (1 + 1 / η) * v ^ 2 - (u + v) ^ 2 := by
      cas using hη.ne'
    rw [halg, show p x + e x = g x by dsimp only [e]; ring] at hnonneg
    linarith)
  rw [intervalIntegral.integral_add (hpI.const_mul _) (heI.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hbound
  have hmodel : (∫ x in a..b, p x ^ 2) =
      (b - a) * g m ^ 2 + (b - a) ^ 3 / 12 * r ^ 2 := by
    dsimp only [p, m]
    cas
  rw [hmodel] at hbound
  exact hbound.trans (by
    have h := mul_le_mul_of_nonneg_left hr
      (show 0 ≤ 1 + 1 / η by positivity)
    dsimp only [m] at h ⊢
    nlinarith)

end PDE.Analysis
