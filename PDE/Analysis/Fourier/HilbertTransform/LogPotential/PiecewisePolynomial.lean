/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Analysis.Fourier.HilbertTransform.LogPotential.Polynomial
public import CAS.Analysis.Approximation.Splines.PiecewisePolynomial
public import PDE.Analysis.Fourier.HilbertTransform.EndpointMoments
import CAS.ExactTactic

/-!
# Finite logarithmic convolutions on a strict mesh

Reflection reduces a compact convolution to the positive panels. Panel identities
are required only on open intervals, so exceptional knot values do not affect the sum.
The logarithmic singularity may lie anywhere, including at a knot or support endpoint.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Polynomial

namespace PDE.Analysis

open CAS.Analysis

/-- Integrable functions telescope over a finite strict mesh. -/
theorem integral_eq_sum_mesh_panels {n : ℕ} (mesh : CAS.Splines.StrictKnotMesh n)
    {g : ℝ → ℝ} (hg : Integrable g) :
    (∫ y in mesh.knot 0..mesh.knot (Fin.last n), g y) =
      ∑ i : Fin n, ∫ y in mesh.panelLeft i..mesh.panelRight i, g y := by
  let A (i : Fin (n + 1)) := ∫ y in mesh.knot 0..mesh.knot i, g y
  have hpanel (i : Fin n) :
      (∫ y in mesh.panelLeft i..mesh.panelRight i, g y) = A i.succ - A i.castSucc :=
    (intervalIntegral.integral_interval_sub_left
      hg.intervalIntegrable hg.intervalIntegrable).symm
  simp_rw [hpanel]
  rw [Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ A
  have hlast := Fin.sum_univ_castSucc A
  have hzero : A 0 = 0 := intervalIntegral.integral_same
  change A (Fin.last n) = _
  linarith

/-- A compact function represented by panel polynomials has an exact finite
logarithmic convolution. The sign `s` records its reflection parity. -/
theorem integral_log_mul_eq_sum_panels {n : ℕ}
    (mesh : CAS.Splines.StrictKnotMesh n) (p : Fin n → ℝ[X])
    {f : ℝ → ℝ} {s x : ℝ} (hzero : mesh.knot 0 = 0)
    (hL : 0 ≤ mesh.knot (Fin.last n))
    (hparity : ∀ y, f (-y) = s * f y)
    (hsupport : ∀ y, mesh.knot (Fin.last n) < y → f y = 0)
    (hpiece : ∀ i y, y ∈ Ioo (mesh.panelLeft i) (mesh.panelRight i) →
      f y = (p i).eval y)
    (hint : Integrable (fun y ↦ Real.log (x - y) * f y)) :
    (∫ y, Real.log (x - y) * f y) =
      ∑ i : Fin n,
        (polynomialLogPanel (p i) (mesh.panelLeft i) (mesh.panelRight i) x +
          s * polynomialLogPanel (p i) (mesh.panelLeft i) (mesh.panelRight i) (-x)) := by
  let g (y : ℝ) := Real.log (x - y) * f y + Real.log (x + y) * f (-y)
  have hg : Integrable g := by
    simpa only [g, sub_neg_eq_add] using hint.fun_add hint.comp_neg
  rw [integral_eq_integral_Ioi_add_reflection hint]
  simp only [sub_neg_eq_add]
  change (∫ y in Ioi 0, g y) = _
  have htruncate :
      (∫ y in Ioi 0, g y) = ∫ y in Ioc 0 (mesh.knot (Fin.last n)), g y := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun _ hy ↦ hy.1)
    intro y hy
    have hyL : mesh.knot (Fin.last n) < y :=
      lt_of_not_ge fun h ↦ hy.2 ⟨hy.1, h⟩
    simp only [g, hparity, hsupport y hyL, mul_zero, add_zero]
  rw [htruncate, ← intervalIntegral.integral_of_le hL, ← hzero,
    integral_eq_sum_mesh_panels mesh hg]
  apply Finset.sum_congr rfl
  intro i _
  have hleft := intervalIntegrable_polynomial_mul_log (p i)
    (mesh.panelLeft i) (mesh.panelRight i) x
  have hright := intervalIntegrable_polynomial_mul_log (p i)
    (mesh.panelLeft i) (mesh.panelRight i) (-x)
  have hlog (z y : ℝ) : Real.log (z - y) = Real.log (y - z) := by
    rw [← Real.log_neg_eq_log (z - y), neg_sub]
  have hleft' : IntervalIntegrable (fun y ↦ (p i).eval y * Real.log (x - y))
      volume (mesh.panelLeft i) (mesh.panelRight i) := by
    simpa only [hlog] using hleft
  have hright' : IntervalIntegrable (fun y ↦ (p i).eval y * Real.log (-x - y))
      volume (mesh.panelLeft i) (mesh.panelRight i) := by
    simpa only [hlog] using hright
  calc
    _ = ∫ y in mesh.panelLeft i..mesh.panelRight i,
        ((p i).eval y * Real.log (x - y) +
          s * ((p i).eval y * Real.log (-x - y))) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (mesh.panelLeft_lt_panelRight i).le
      intro y hy
      simp only [g, hparity, hpiece i y hy]
      rw [show -x - y = -(x + y) by cas, Real.log_neg_eq_log]
      cas
    _ = _ := by
      rw [intervalIntegral.integral_add hleft' (hright'.const_mul s),
        intervalIntegral.integral_const_mul,
        integral_polynomial_mul_log_sub, integral_polynomial_mul_log_sub]

end PDE.Analysis
