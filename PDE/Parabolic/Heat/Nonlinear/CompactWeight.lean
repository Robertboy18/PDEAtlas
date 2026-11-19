/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.AbsolutelyContinuous.PowerGrowth
public import PDE.Analysis.MeasureTheory.Integral.WeightedJensen
public import PDE.DistributionTheory.TestFunction.IntegrationByParts
public import PDE.FDeriv.Laplacian.Continuity
import PDE.FDeriv.Laplacian.Congruence
import PDE.Analysis.Calculus.CompactParametricIntegral.Interval
import PDE.Analysis.Evolution.LionsMagenes.Basic.WeakDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Compact moments of whole-space nonlinear heat solutions

A compactly supported spatial weight permits differentiation and two integrations
by parts using only local classical regularity. In particular, no spatial decay
of the solution's derivatives is required. A lower bound for the weight's
Laplacian and Jensen's inequality yield the damped power-growth inequality.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PDE (laplacian)
open PDE.Analysis PDE.Analysis.Evolution

namespace HeatEquation.Nonlinear

variable {n : ℕ} {T p : ℝ}

/-- A nonnegative classical solution of `uₜ - Δu = uᵖ` on a finite whole-space
cylinder `[0, T] × ℝⁿ`, with initial data `g` and time derivative `D`. The regularity is
local in space, with continuous initial traces.
No weighted moment, integrability, or decay condition is part of this definition.

The singularity theory uses
`PDE.Solution.Singularity.FiniteTime.NonlinearHeat.IsNonnegativePointwiseClassicalSolutionOn`
instead: an open time domain, no initial data, and joint `C¹` regularity. -/
structure IsClassicalWholeSpacePowerSolution (p T : ℝ) (g : ℝ^n → ℝ)
    (u D : ℝ → ℝ^n → ℝ) : Prop where
  /-- Joint continuity including the initial time. -/
  continuous : ContinuousOn u.uncurry (Icc 0 T ×ˢ univ)
  /-- The time derivative is jointly continuous only at positive interior times. -/
  continuous_derivative : ContinuousOn D.uncurry (Ioo 0 T ×ˢ univ)
  /-- Twice continuously differentiable spatial slices. -/
  space : ∀ t ∈ Ioo 0 T, ContDiff ℝ 2 (u t)
  /-- The time derivative in the open cylinder. -/
  time : ∀ x, ∀ t ∈ Ioo 0 T, HasDerivAt (fun r ↦ u r x) (D t x) t
  /-- The whole-space nonlinear heat equation. -/
  equation : ∀ t ∈ Ioo 0 T, ∀ x, D t x - laplacian (u t) x = u t x ^ p
  /-- Nonnegativity is the solution class in Fujita's theorem. -/
  nonneg : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ u t x
  /-- Initial values at every spatial point. -/
  initial : ∀ x, u 0 x = g x

/-- An interior `C²` solution with continuous initial values supplies the classical
predicate. Its time derivative is constructed from the derivative; no
continuity of this derivative at either time face is required. -/
theorem IsClassicalWholeSpacePowerSolution.of_contDiffOn
    {g : ℝ^n → ℝ} {u : ℝ → ℝ^n → ℝ}
    (hc : ContinuousOn u.uncurry (Icc 0 T ×ˢ univ))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioo 0 T ×ˢ univ))
    (heq : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ p)
    (hn : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ u t x)
    (hinit : ∀ x, u 0 x = g x) :
    IsClassicalWholeSpacePowerSolution p T g u (fun t x ↦ deriv (fun r ↦ u r x) t) := by
  have hopen : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set (ℝ^n))) := isOpen_Ioo.prod isOpen_univ
  have hd (t : ℝ) (ht : t ∈ Ioo 0 T) (x : ℝ^n) :
      HasDerivAt (fun r ↦ u r x) (fderiv ℝ u.uncurry (t, x) (1, 0)) t := by
    exact ((hs.contDiffAt (hopen.mem_nhds ⟨ht, mem_univ x⟩)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  refine ⟨hc, ?_, ?_, fun x t ht ↦ (hd t ht x).deriv ▸ hd t ht x, heq, hn, hinit⟩
  · have hD : ContinuousOn (fun q ↦ fderiv ℝ u.uncurry q (1, 0))
        (Ioo 0 T ×ˢ univ) :=
      (hs.continuousOn_fderiv_of_isOpen hopen (by norm_num)).clm_apply
        continuous_const.continuousOn
    exact hD.congr fun q hq ↦ (hd q.1 hq.1 q.2).deriv
  · intro t ht
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (hs.contDiffAt (hopen.mem_nhds ⟨ht, mem_univ x⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)

/-- Continuity of the solution alone gives the initial trace of every compact moment. -/
theorem IsClassicalWholeSpacePowerSolution.compact_moment_continuous
    {g w : ℝ^n → ℝ} {u D : ℝ → ℝ^n → ℝ}
    (hu : IsClassicalWholeSpacePowerSolution p T g u D)
    (hw : Continuous w) (hcpt : HasCompactSupport w) :
    ContinuousOn (fun t ↦ ∫ x, w x * u t x) (Icc 0 T) := by
  have hf : ContinuousOn (fun q : ℝ × ℝ^n ↦ w q.2 * u q.1 q.2)
      (Icc 0 T ×ˢ closure (tsupport w)) :=
    (hw.comp continuous_snd).continuousOn.mul
      (hu.continuous.mono (fun _ h ↦ ⟨h.1, mem_univ _⟩))
  have hcont := PDE.continuousOn_setIntegral_of_compact_interval
    (μ := volume) (f := fun t x ↦ w x * u t x) (isClosed_tsupport w).measurableSet
    hcpt.closure hcpt.measure_lt_top.ne hf
  have heq (t : ℝ) : (∫ x in tsupport w, w x * u t x) = ∫ x, w x * u t x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  simpa only [heq] using hcont

/-- Compact moments are absolutely continuous on every closed interval strictly
inside the positive-time cylinder. No time derivative trace at zero is used. -/
theorem IsClassicalWholeSpacePowerSolution.compact_moment_regularity
    {g w : ℝ^n → ℝ} {u D : ℝ → ℝ^n → ℝ}
    (hu : IsClassicalWholeSpacePowerSolution p T g u D) {a b : ℝ}
    (ha : 0 < a) (hb : b < T) (hab : a ≤ b)
    (hw : Continuous w) (hcpt : HasCompactSupport w) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ x, w x * u t x) a b ∧
      ∀ t ∈ Ioo a b, HasDerivAt (fun r ↦ ∫ x, w x * u r x)
        (∫ x, w x * D t x) t := by
  have hs : Icc a b ⊆ Ioo 0 T := Icc_subset_Ioo ha hb
  have hf : ContinuousOn (fun q : ℝ × ℝ^n ↦ w q.2 * u q.1 q.2)
      (Icc a b ×ˢ closure (tsupport w)) :=
    (hw.comp continuous_snd).continuousOn.mul
      (hu.continuous.mono (fun _ h ↦ ⟨Ioo_subset_Icc_self (hs h.1), mem_univ _⟩))
  have hD : ContinuousOn (fun q : ℝ × ℝ^n ↦ w q.2 * D q.1 q.2)
      (Icc a b ×ˢ closure (tsupport w)) :=
    (hw.comp continuous_snd).continuousOn.mul
      (hu.continuous_derivative.mono (fun _ h ↦ ⟨hs h.1, mem_univ _⟩))
  have heq (f : ℝ^n → ℝ) : (∫ x in tsupport w, w x * f x) = ∫ x, w x * f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hcont := PDE.continuousOn_setIntegral_of_compact_interval
    (μ := volume) (f := fun t x ↦ w x * u t x) (isClosed_tsupport w).measurableSet
    hcpt.closure hcpt.measure_lt_top.ne hf
  have hDcont := PDE.continuousOn_setIntegral_of_compact_interval
    (μ := volume) (f := fun t x ↦ w x * D t x) (isClosed_tsupport w).measurableSet
    hcpt.closure hcpt.measure_lt_top.ne hD
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :=
    PDE.hasDerivAt_setIntegral_of_compact_interval
      (μ := volume) (f := fun t x ↦ w x * u t x) (D := fun t x ↦ w x * D t x)
      (isClosed_tsupport w).measurableSet hcpt.closure hcpt.measure_lt_top.ne hf hD
      (fun x _ r hr ↦ (hu.time x r (hs (Ioo_subset_Icc_self hr))).const_mul (w x)) ht
  simp_rw [heq] at hcont hDcont hd
  refine ⟨?_, hd⟩
  apply absolutelyContinuousOnInterval_of_eq_add_integral (hDcont.intervalIntegrable_of_Icc hab)
  intro t ht
  rw [uIcc_of_le hab] at ht
  have hst : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hcont.mono hst) (fun r hr ↦ hd r ⟨hr.1, hr.2.trans_le ht.2⟩)
    ((hDcont.mono hst).intervalIntegrable_of_Icc ht.1)
  linarith

/-- Differentiate a compact moment at an interior time by first localizing to
an interval contained in the open cylinder. -/
theorem IsClassicalWholeSpacePowerSolution.hasDerivAt_compact_moment
    {g w : ℝ^n → ℝ} {u D : ℝ → ℝ^n → ℝ}
    (hu : IsClassicalWholeSpacePowerSolution p T g u D)
    (hw : Continuous w) (hcpt : HasCompactSupport w) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r ↦ ∫ x, w x * u r x) (∫ x, w x * D t x) t := by
  exact (hu.compact_moment_regularity (a := t / 2) (b := (t + T) / 2)
    (by linarith [ht.1]) (by linarith [ht.2]) (by linarith [ht.1, ht.2])
      hw hcpt).2 t ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- The whole-space PDE implies damped power growth for every compact probability
weight satisfying `Δw ≥ -λw`. All integration by parts is over the whole space. -/
theorem IsClassicalWholeSpacePowerSolution.compact_moment_inequality
    {g w : ℝ^n → ℝ} {u D : ℝ → ℝ^n → ℝ} {lambda : ℝ}
    (hu : IsClassicalWholeSpacePowerSolution p T g u D) (hp : 1 < p)
    (hw : ContDiff ℝ 2 w) (hcpt : HasCompactSupport w)
    (hwpos : ∀ x, 0 ≤ w x) (hunit : ∫ x, w x = 1)
    (hlap : ∀ x, -lambda * w x ≤ laplacian w x)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    (∫ x, w x * u t x) ^ p ≤
      deriv (fun r ↦ ∫ x, w x * u r x) t + lambda * ∫ x, w x * u t x := by
  have htc := Ioo_subset_Icc_self ht
  have huc := (hu.space t ht).continuous
  have hiw : Integrable w := hw.continuous.integrable_of_hasCompactSupport hcpt
  have hiu : Integrable (fun x ↦ w x * u t x) :=
    (hw.continuous.mul huc).integrable_of_hasCompactSupport hcpt.mul_right
  have hiR : Integrable (fun x ↦ w x * u t x ^ p) :=
    Continuous.integrable_of_hasCompactSupport
      (hw.continuous.mul (huc.rpow_const (fun _ ↦ Or.inr (by linarith)))) hcpt.mul_right
  have hiL : Integrable (fun x ↦ w x * laplacian (u t) x) :=
    Continuous.integrable_of_hasCompactSupport
      (hw.continuous.mul (hu.space t ht).continuous_coordinate_laplacian) hcpt.mul_right
  have hiLw : Integrable (fun x ↦ laplacian w x * u t x) :=
    Continuous.integrable_of_hasCompactSupport
      (hw.continuous_coordinate_laplacian.mul huc) hcpt.coordinate_laplacian.mul_right
  have hj := convex_map_integral_mul_le (Filter.Eventually.of_forall hwpos) hunit
    hiu (Filter.Eventually.of_forall (hu.nonneg t htc)) hiR (convexOn_rpow hp.le)
  have hibp := PDE.DistributionTheory.integral_mul_laplacian_eq (u t) hw (hu.space t ht) hcpt
  have hdiffusion : -lambda * (∫ x, w x * u t x) ≤ ∫ x, w x * laplacian (u t) x := by
    rw [hibp, ← integral_const_mul]
    exact integral_mono (hiu.const_mul (-lambda)) hiLw (fun x ↦ by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hlap x) (hu.nonneg t htc x))
  have hid : (∫ x, w x * D t x) =
      (∫ x, w x * laplacian (u t) x) + ∫ x, w x * u t x ^ p := by
    rw [← integral_add hiL hiR]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      have heq := hu.equation t ht x
      linear_combination w x * heq
  rw [(hu.hasDerivAt_compact_moment hw.continuous hcpt ht).deriv,
    hid]
  linarith

/-- Every global nonnegative classical whole-space solution obeys the sharp
necessary bound on each compact probability-weighted initial moment. -/
theorem initial_compact_moment_bound
    {g w : ℝ^n → ℝ} {lambda : ℝ} (hp : 1 < p) (hlambda : 0 < lambda)
    (hw : ContDiff ℝ 2 w) (hcpt : HasCompactSupport w)
    (hwpos : ∀ x, 0 ≤ w x) (hunit : ∫ x, w x = 1)
    (hlap : ∀ x, -lambda * w x ≤ laplacian w x)
    (hm : 0 < ∫ x, w x * g x)
    (hglobal : ∀ T : ℝ, 0 < T → ∃ u D, IsClassicalWholeSpacePowerSolution p T g u D) :
    1 ≤ lambda * (∫ x, w x * g x) ^ (1 - p) := by
  apply le_mul_rpow_of_global_local_damped_power_trajectories hm zero_le_one hp hlambda
  intro T hT
  obtain ⟨u, D, hu⟩ := hglobal (T + 1) (by linarith)
  refine ⟨fun t ↦ ∫ x, w x * u t x,
    (hu.compact_moment_continuous hw.continuous hcpt).mono
      (Icc_subset_Icc le_rfl (by linarith)), ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact (hu.compact_moment_regularity ha.1 (by linarith) ha.2 hw.continuous hcpt).1
  · simp_rw [hu.initial]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact integral_nonneg (fun x ↦ mul_nonneg (hwpos x)
      (hu.nonneg t ⟨ht.1.le, by linarith [ht.2]⟩ x))
  · rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simpa only [one_mul] using hu.compact_moment_inequality hp hw hcpt hwpos hunit hlap
      ⟨ht.1, by linarith [ht.2]⟩

end HeatEquation.Nonlinear
