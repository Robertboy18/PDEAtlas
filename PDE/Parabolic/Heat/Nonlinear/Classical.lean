/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.AbsolutelyContinuous.PowerGrowth
public import PDE.Analysis.MeasureTheory.Integral.WeightedJensen
public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.ZeroBoundary
public import PDE.Parabolic.Heat.MaximumPrinciple
import PDE.Analysis.Calculus.CompactParametricIntegral.Interval
import PDE.Analysis.Evolution.LionsMagenes.Basic.WeakDerivative
import CAS.ExactTactic

/-!
# Classical quadratic heat blowup on a bounded domain

Let `Ω` be a bounded open set with `C¹` graph boundary, and let `w ≥ 0` be a Dirichlet eigenfunction
of `-Δ` with eigenvalue `λ > 0` that is `C²` up to the boundary and normalized by `∫ w = 1`. If
`g ≥ 0` and `∫ w g > λ`, then some finite cylinder `[0, T] × Ω` carries no classical solution of
`uₜ - Δu = u²` with zero boundary values and initial value `g`
(`not_forall_exists_isClassicalDirichletSquareSolution`). Regularity is stated on each closed finite
cylinder. Spatial derivatives are one-sided closure jets; no extension across the boundary is
assumed.

This is Evans's §9.4.1, Theorem 1, for nonnegative data, with `w` in the role of his normalized
principal eigenfunction `w₁` of (2).

## How it works

As in Evans's proof, the moment `η(t) = ∫ w u(t)` satisfies a scalar differential inequality. It is
absolutely continuous (`absolutelyContinuousOnInterval_classical_weighted_moment`). Green's identity
moves the Laplacian onto `w`, and Jensen's inequality for the probability measure `w dx`, in place
of Evans's Cauchy-Schwarz step, gives `η' ≥ -λη + η²`, his (5)
(`IsClassicalDirichletSquareSolution.moment_inequality`). Nonnegative data make `u` nonnegative by
the minimum principle (`IsClassicalDirichletSquareSolution.nonneg`), which the moment inequality and
the scalar comparison use. The scalar comparison `le_mul_rpow_of_global_damped_power_trajectories`,
in place of Evans's integration of `ξ = e^{λ₁t} η`, shows that a trajectory that exists on every
`[0, T]` has `η(0) ≤ λ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.1, (1)-(2), p. 547, and Theorem 1 (Blow-up for large
  data) and its proof, (3)-(5), pp. 548-549.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace
open PDE (laplacian)
open PDE.Analysis PDE.Analysis.Evolution

namespace HeatEquation.Nonlinear

variable {n : ℕ} {Ω : Set (ℝ^n)} {T : ℝ}

/-- Classical data for `uₜ - Δu = u²` on a finite Dirichlet cylinder.
The time derivative is a continuous closure jet, identified with the interior
derivative. No scalar moment identity is included. -/
structure IsClassicalDirichletSquareSolution (Ω : Set (ℝ^n)) (T : ℝ)
    (g : ℝ^n → ℝ) (u D : ℝ → ℝ^n → ℝ) : Prop where
  /-- Continuity including the initial and lateral faces. -/
  continuous : ContinuousOn u.uncurry (Icc 0 T ×ˢ closure Ω)
  /-- The time derivative extends continuously to the closed cylinder. -/
  continuous_derivative : ContinuousOn D.uncurry (Icc 0 T ×ˢ closure Ω)
  /-- Two spatial derivatives up to the boundary at positive interior times. -/
  space : ∀ t ∈ Ioo 0 T, ContDiffUpToBoundary 2 (u t) Ω
  /-- Time differentiation is needed only in the open cylinder. -/
  time : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, HasDerivAt (fun r ↦ u r x) (D t x) t
  /-- The quadratic nonlinear heat equation. -/
  equation : ∀ t ∈ Ioo 0 T, ∀ x ∈ Ω, D t x - laplacian (u t) x = u t x ^ 2
  /-- Homogeneous Dirichlet boundary values. -/
  boundary : ∀ x ∈ frontier Ω, ∀ t ∈ Icc 0 T, u t x = 0
  /-- Initial values on the spatial closure. -/
  initial : ∀ x ∈ closure Ω, u 0 x = g x

/-- A classical heat supersolution with nonnegative initial data stays nonnegative.
For the quadratic reaction, the supersolution property follows without a sign
assumption on the candidate solution. -/
theorem IsClassicalDirichletSquareSolution.nonneg
    {g : ℝ^n → ℝ} {u D : ℝ → ℝ^n → ℝ}
    (hu : IsClassicalDirichletSquareSolution Ω T g u D)
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω) (hT : 0 < T)
    (hg : ∀ x ∈ closure Ω, 0 ≤ g x) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ closure Ω, 0 ≤ u t x := by
  have hc : ContinuousOn (fun p : ℝ^n × ℝ ↦ u p.2 p.1)
      (ParabolicMaximum.closedCylinder Ω T) :=
    hu.continuous.comp continuous_swap.continuousOn (fun _ hp ↦ ⟨hp.2, hp.1⟩)
  have h := boundary_le_heat_supersolution hΩ hne hb.isCompact_closure hT
    (fun x t ↦ u t x) hc
    (fun x hx t ht ↦ (hu.space t ht).contDiffOn.contDiffAt (hΩ.mem_nhds hx))
    (fun x hx t ht ↦ (hu.time x hx t ht).differentiableAt)
    (fun x hx t ht ↦ by
      change 0 ≤ deriv (fun r ↦ u r x) t - laplacian (u t) x
      rw [(hu.time x hx t ht).deriv, hu.equation t ht x hx]
      exact sq_nonneg _) (M := 0) (by
        intro p hp
        rcases hp with hp | hp
        · rw [hu.boundary p.1 hp.1 p.2 hp.2]
        · have hz : p.2 = 0 := hp.2
          rw [hz, hu.initial p.1 hp.1]
          exact hg p.1 hp.1)
  exact fun t ht x hx ↦ h (x, t) ⟨hx, ht⟩

/-- Continuous closure values and time derivatives make a bounded-domain
weighted moment absolutely continuous, including the endpoint traces. -/
theorem absolutelyContinuousOnInterval_classical_weighted_moment
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hT : 0 ≤ T)
    {w : ℝ^n → ℝ} (hw : ContinuousOn w (closure Ω))
    {u D : ℝ → ℝ^n → ℝ}
    (hu : ContinuousOn u.uncurry (Icc 0 T ×ˢ closure Ω))
    (hD : ContinuousOn D.uncurry (Icc 0 T ×ˢ closure Ω))
    (hd : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, HasDerivAt (fun r ↦ u r x) (D t x) t) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ x in Ω, w x * u t x) 0 T := by
  have hwc : ContinuousOn (fun p : ℝ × ℝ^n ↦ w p.2) (Icc 0 T ×ˢ closure Ω) :=
    hw.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  have hc := PDE.continuousOn_setIntegral_of_compact_interval
    (μ := volume) (f := fun t x ↦ w x * u t x) hΩ.measurableSet
    hb.isCompact_closure hb.measure_lt_top.ne (hwc.mul hu)
  have hdc := PDE.continuousOn_setIntegral_of_compact_interval
    (μ := volume) (f := fun t x ↦ w x * D t x) hΩ.measurableSet
    hb.isCompact_closure hb.measure_lt_top.ne (hwc.mul hD)
  have hderiv (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt (fun r ↦ ∫ x in Ω, w x * u r x) (∫ x in Ω, w x * D t x) t :=
    PDE.hasDerivAt_setIntegral_of_compact_interval
      (μ := volume) (f := fun t x ↦ w x * u t x) (D := fun t x ↦ w x * D t x)
      hΩ.measurableSet hb.isCompact_closure
      hb.measure_lt_top.ne (hwc.mul hu) (hwc.mul hD)
      (fun x hx r hr ↦ (hd x hx r hr).const_mul (w x)) ht
  apply absolutelyContinuousOnInterval_of_eq_add_integral (hdc.intervalIntegrable_of_Icc hT)
  intro t ht
  rw [uIcc_of_le hT] at ht
  have hs : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hc.mono hs) (fun r hr ↦ hderiv r ⟨hr.1, hr.2.trans_le ht.2⟩)
    ((hdc.mono hs).intervalIntegrable_of_Icc ht.1)
  linarith

/-- Green's identity and Jensen derive the quadratic eigenfunction-moment
inequality directly from a classical nonlinear heat solution. -/
theorem IsClassicalDirichletSquareSolution.moment_inequality
    [Fact (0 < n)] {g w : ℝ^n → ℝ} {u D : ℝ → ℝ^n → ℝ} {lambda : ℝ}
    (hu : IsClassicalDirichletSquareSolution Ω T g u D)
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hw : ContDiffUpToBoundary 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0)
    (hwpos : ∀ x ∈ Ω, 0 ≤ w x) (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hnonneg : ∀ t ∈ Icc 0 T, ∀ x ∈ closure Ω, 0 ≤ u t x)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    (∫ x in Ω, w x * u t x) ^ 2 ≤
      deriv (fun r ↦ ∫ x in Ω, w x * u r x) t + lambda * ∫ x in Ω, w x * u t x := by
  have htc : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have huc : ContinuousOn (u t) (closure Ω) :=
    hu.continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx ↦ ⟨htc, hx⟩)
  have hdc : ContinuousOn (D t) (closure Ω) :=
    hu.continuous_derivative.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx ↦ ⟨htc, hx⟩)
  have hint {f : ℝ^n → ℝ} (hf : ContinuousOn f (closure Ω)) : IntegrableOn f Ω :=
    hf.integrableOn_of_subset_isCompact hb.isCompact_closure hΩ.measurableSet
      subset_closure hb.measure_lt_top.ne
  have hj := convex_map_integral_mul_le
    (ae_restrict_mem hΩ.measurableSet |>.mono fun x hx ↦ hwpos x hx) hunit
    (hint (hwc.mul huc))
    (ae_restrict_mem hΩ.measurableSet |>.mono fun x hx ↦ hnonneg t htc x (subset_closure hx))
    (hint (hwc.mul (huc.pow 2)))
    (by simpa only [Real.rpow_two] using (convexOn_rpow (p := 2) (by norm_num)))
  have hgreen₁ := integral_sum_partialDeriv_mul_eq_neg_laplacian hΩ hb hgraph
    (hu.space t ht) (hw.of_le (by omega)) hwc hwzero
  have hgreen₂ := integral_sum_partialDeriv_mul_eq_neg_laplacian hΩ hb hgraph
    hw ((hu.space t ht).of_le (by omega)) huc (fun x hx ↦ hu.boundary x hx t htc)
  have hgreen : (∫ x in Ω, w x * laplacian (u t) x) =
      ∫ x in Ω, laplacian w x * u t x := by
    simp only [mul_comm] at hgreen₁ hgreen₂ ⊢
    linarith
  have hdiffusion : (∫ x in Ω, w x * laplacian (u t) x) =
      -lambda * ∫ x in Ω, w x * u t x := by
    rw [hgreen, ← integral_const_mul]
    exact setIntegral_congr_fun hΩ.measurableSet fun x hx ↦ by rw [heigen x hx, mul_assoc]
  have hsplit : (fun x ↦ w x * laplacian (u t) x) =ᵐ[volume.restrict Ω]
      (fun x ↦ w x * D t x - w x * u t x ^ 2) := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    have heq := hu.equation t ht x hx
    linear_combination -w x * heq
  have hiD : IntegrableOn (fun x ↦ w x * D t x) Ω := hint (hwc.mul hdc)
  have hiR : IntegrableOn (fun x ↦ w x * u t x ^ 2) Ω := hint (hwc.mul (huc.pow 2))
  have hid : (∫ x in Ω, w x * D t x) =
      (∫ x in Ω, w x * laplacian (u t) x) + ∫ x in Ω, w x * u t x ^ 2 := by
    rw [integral_congr_ae hsplit, integral_sub hiD hiR]
    linarith
  have hwjoint : ContinuousOn (fun p : ℝ × ℝ^n ↦ w p.2) (Icc 0 T ×ˢ closure Ω) :=
    hwc.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  have hd := PDE.hasDerivAt_setIntegral_of_compact_interval
      (μ := volume) (f := fun t x ↦ w x * u t x) (D := fun t x ↦ w x * D t x)
      hΩ.measurableSet hb.isCompact_closure
    hb.measure_lt_top.ne (hwjoint.mul hu.continuous) (hwjoint.mul hu.continuous_derivative)
    (fun x hx r hr ↦ (hu.time x hx r hr).const_mul (w x)) ht
  rw [hd.deriv, hid, hdiffusion]
  linarith

/-- Above the first-eigenfunction threshold, some finite cylinder `[0, T] × Ω` carries no
classical Dirichlet solution with nonnegative data `g`. All moment hypotheses are
consequences of the PDE, Green's identity and the heat minimum principle. The weight `w` is a
nonnegative normalized Dirichlet eigenfunction that is `C²` up to the boundary, in the role of
the normalized principal eigenfunction `w₁` of Evans's §9.4.1, Theorem 1. -/
theorem not_forall_exists_isClassicalDirichletSquareSolution
    [Fact (0 < n)] {g w : ℝ^n → ℝ} {lambda : ℝ}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hw : ContDiffUpToBoundary 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0)
    (hwpos : ∀ x ∈ Ω, 0 ≤ w x) (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hlambda : 0 < lambda) (hg : ∀ x ∈ closure Ω, 0 ≤ g x)
    (hlarge : lambda < ∫ x in Ω, w x * g x) :
    ¬ ∀ T : ℝ, 0 < T → ∃ u D, IsClassicalDirichletSquareSolution Ω T g u D := by
  intro hglobal
  have hm := hlambda.trans hlarge
  have hbound := le_mul_rpow_of_global_damped_power_trajectories
    (c := 1) (p := 2) hm (by norm_num) (by norm_num) hlambda (by
      intro T hT
      obtain ⟨u, D, hu⟩ := hglobal T hT
      have hn := hu.nonneg hΩ hne hb hT hg
      refine ⟨fun t ↦ ∫ x in Ω, w x * u t x,
        absolutelyContinuousOnInterval_classical_weighted_moment hΩ hb hT.le hwc
          hu.continuous hu.continuous_derivative hu.time, ?_, ?_, ?_⟩
      · apply setIntegral_congr_fun hΩ.measurableSet
        intro x hx
        dsimp only
        rw [hu.initial x (subset_closure hx)]
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
        exact mul_nonneg (hwpos x hx) (hn t ⟨ht.1.le, ht.2⟩ x (subset_closure hx))
      · rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        simpa only [one_mul, Real.rpow_two] using
          hu.moment_inequality hΩ hb hgraph hw hwc hwzero hwpos hunit heigen hn ht)
  norm_num only [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one,
    ← div_eq_mul_inv] at hbound
  have hle := (le_div_iff₀ hm).mp hbound
  exact (not_le_of_gt hlarge) (by simpa only [one_mul] using hle)

end HeatEquation.Nonlinear
