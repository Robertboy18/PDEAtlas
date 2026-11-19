/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Nonlinear.ConvexTruncation
public import PDE.FDeriv.Calculus.ScalarComposition
import PDE.FDeriv.Laplacian.Congruence

/-!
# Interior approximations of a Dirichlet eigenfunction

A positive threshold removes a neighborhood of the boundary before spatial
integration by parts. The resulting compact `C²` tests retain a lower Laplacian
bound with an error tending uniformly to zero. No boundary derivative of the
solution is used.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE (laplacian)
open scoped Topology

namespace HeatEquation.Nonlinear

variable {n : ℕ} {Ω : Set (ℝ^n)} {w : ℝ^n → ℝ} {ε : ℝ}

/-- Convex truncation of the zero extension of a Dirichlet weight. -/
def dirichletTest (Ω : Set (ℝ^n)) (w : ℝ^n → ℝ) (ε : ℝ) (x : ℝ^n) : ℝ :=
  convexTruncation ε (Ω.indicator w x)

/-- The truncated weight agrees with its interior formula near every interior point. -/
theorem dirichletTest_eventuallyEq (hΩ : IsOpen Ω) {x : ℝ^n} (hx : x ∈ Ω) :
    dirichletTest Ω w ε =ᶠ[𝓝 x] fun y ↦ convexTruncation ε (w y) := by
  filter_upwards [hΩ.mem_nhds hx] with y hy
  simp only [dirichletTest, indicator_of_mem hy]

/-- The positive threshold puts the closed support strictly inside the domain. -/
theorem tsupport_dirichletTest_subset (hε : 0 < ε)
    (hwc : ContinuousOn w (closure Ω)) (hwzero : ∀ x ∈ frontier Ω, w x = 0) :
    tsupport (dirichletTest Ω w ε) ⊆ Ω := by
  have hc : Continuous (Ω.indicator w) := continuous_indicator hwzero hwc
  have hs : tsupport (dirichletTest Ω w ε) ⊆ {x | ε ≤ Ω.indicator w x} := by
    apply closure_minimal _ (isClosed_le continuous_const hc)
    intro x hx
    by_contra h
    exact hx (convexTruncation_eq_zero hε (le_of_not_ge h))
  intro x hx
  by_contra hn
  have h : ε ≤ Ω.indicator w x := hs hx
  rw [indicator_of_notMem hn] at h
  exact hε.not_ge h

/-- Bounded domains give compact support for the truncated weight. -/
theorem hasCompactSupport_dirichletTest (hb : Bornology.IsBounded Ω) (hε : 0 < ε)
    (hwc : ContinuousOn w (closure Ω)) (hwzero : ∀ x ∈ frontier Ω, w x = 0) :
    HasCompactSupport (dirichletTest Ω w ε) :=
  hb.isCompact_closure.of_isClosed_subset (isClosed_tsupport _)
    ((tsupport_dirichletTest_subset hε hwc hwzero).trans subset_closure)

/-- Interior `C²` regularity and zero continuous boundary values suffice to make
the truncated weight globally `C²`. No derivative extension of the weight is needed. -/
theorem contDiff_dirichletTest (hΩ : IsOpen Ω) (hε : 0 < ε)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) :
    ContDiff ℝ 2 (dirichletTest Ω w ε) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ Ω
  · exact ((contDiff_convexTruncation ε).contDiffAt.comp x
      (hw.contDiffAt (hΩ.mem_nhds hx))).congr_of_eventuallyEq
        (dirichletTest_eventuallyEq hΩ hx)
  · have hn : x ∉ tsupport (dirichletTest Ω w ε) :=
      fun h ↦ hx (tsupport_dirichletTest_subset hε hwc hwzero h)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)

/-- The truncated weight is nonnegative and no larger than the original weight. -/
theorem dirichletTest_bounds (hwpos : ∀ x ∈ Ω, 0 ≤ w x) (x : ℝ^n) :
    0 ≤ dirichletTest Ω w ε x ∧ dirichletTest Ω w ε x ≤ Ω.indicator w x := by
  exact convexTruncation_bounds (indicator_nonneg hwpos x)

/-- The interior truncation has uniformly small error. -/
theorem sub_two_mul_le_dirichletTest (hε : 0 < ε)
    (hwpos : ∀ x ∈ Ω, 0 ≤ w x) {x : ℝ^n} (hx : x ∈ Ω) :
    w x - 2 * ε ≤ dirichletTest Ω w ε x := by
  simpa only [dirichletTest, indicator_of_mem hx] using
    sub_two_mul_le_convexTruncation hε (hwpos x hx)

/-- The eigenfunction equation survives interior truncation with a uniform
additive error. This estimate needs no spatial derivative of the solution. -/
theorem neg_mul_dirichletTest_le_laplacian {lambda : ℝ}
    (hΩ : IsOpen Ω) (hε : 0 < ε) (hlambda : 0 ≤ lambda)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 ≤ w x)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x) (x : ℝ^n) :
    -lambda * dirichletTest Ω w ε x - 2 * lambda * ε ≤
      laplacian (dirichletTest Ω w ε) x := by
  by_cases hx : x ∈ Ω
  · rw [EuclideanLaplacian.laplacian_congr_nhds (dirichletTest_eventuallyEq hΩ hx),
      PDE.laplacian_comp_real (contDiff_convexTruncation ε).contDiffAt
        (hw.contDiffAt (hΩ.mem_nhds hx)), heigen x hx]
    have hd : deriv (convexTruncation ε) (w x) ≤ 1 := by
      rw [(hasDerivAt_convexTruncation ε (w x)).deriv]
      exact Real.smoothTransition.le_one _
    have hprod := mul_le_mul_of_nonpos_right hd
      (neg_nonpos.mpr (mul_nonneg hlambda (hwpos x hx)))
    have hsecond := mul_nonneg (deriv_deriv_convexTruncation_nonneg hε (w x))
      (sq_nonneg ‖gradient w x‖)
    have happ := mul_le_mul_of_nonneg_left
      (sub_two_mul_le_dirichletTest hε hwpos hx) hlambda
    nlinarith
  · have hn : x ∉ tsupport (dirichletTest Ω w ε) :=
      fun h ↦ hx (tsupport_dirichletTest_subset hε hwc hwzero h)
    rw [EuclideanLaplacian.laplacian_eq_zero_of_notMem_tsupport hn,
      image_eq_zero_of_notMem_tsupport hn]
    nlinarith [mul_nonneg hlambda hε.le]

end HeatEquation.Nonlinear
