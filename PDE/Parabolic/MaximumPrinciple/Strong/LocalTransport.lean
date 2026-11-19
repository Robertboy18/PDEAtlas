/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.MaximumPrinciple.Strong.BarrierComparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Local forward transport of positivity

A positive value provides a small initial polynomial bump. Compactness bounds
the continuous coefficients on the entire slab, fixing one decay parameter
before comparison. The same bump remains strictly positive at its moving
center at the terminal time.
-/

@[expose] public section

noncomputable section

namespace ParabolicMaximum

open PDE.Analysis Set Metric Filter
open scoped Topology RealInnerProductSpace

variable {n : ℕ}

/-- A nonnegative supersolution stays positive along any affine motion whose
travel fits in the inner half of the comparison ball. Coefficient bounds and
the barrier are derived from continuity and ellipticity. -/
theorem positive_at_moving_center
    {y : ℝ^n} {r s t θ : ℝ} (hr : 0 < r) (hst : s < t) (hθ : 0 < θ)
    (v : ℝ^n) (htravel : (t - s) * ‖v‖ ≤ r)
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    (htrace : ContinuousOn (fun p : ℝ^n × ℝ ↦ (a p.1 p.2).trace)
      (closedBall y (2 * r) ×ˢ Icc s t))
    (hb : ContinuousOn (fun p : ℝ^n × ℝ ↦ b p.1 p.2)
      (closedBall y (2 * r) ×ˢ Icc s t))
    (hccont : ContinuousOn (fun p : ℝ^n × ℝ ↦ c p.1 p.2)
      (closedBall y (2 * r) ×ˢ Icc s t))
    (ha : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t, (a x q).PosSemidef)
    (hell : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t, ∀ d : ℝ^n,
      θ * ‖d‖ ^ 2 ≤ ⟪d, (a x q).toEuclideanLin d⟫)
    (hc : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t, 0 ≤ c x q)
    (w : ℝ^n → ℝ → ℝ)
    (hwcont : ContinuousOn (fun p : ℝ^n × ℝ ↦ w p.1 p.2)
      (closedBall y (2 * r) ×ˢ Icc s t))
    (hwspace : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t,
      ContDiffAt ℝ 2 (fun z ↦ w z q) x)
    (hwtime : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t, DifferentiableAt ℝ (w x) q)
    (hwsuper : ∀ x ∈ ball y (2 * r), ∀ q ∈ Ioo s t,
      0 ≤ matrixParabolicOperator a b c w x q)
    (hwnonneg : ∀ x ∈ closedBall y (2 * r), ∀ q ∈ Icc s t, 0 ≤ w x q)
    (hwpos : 0 < w y s) :
    0 < w (y + (t - s) • v) t := by
  let K : Set (ℝ^n × ℝ) := closedBall y (2 * r) ×ˢ Icc s t
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn htrace
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hb
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hccont
  have hslice : ContinuousOn (fun x ↦ w x s) (closedBall y (2 * r)) :=
    hwcont.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun x hx ↦ ⟨hx, le_rfl, hst.le⟩)
  have hstart : ContinuousAt (fun x ↦ w x s) y :=
    hslice.continuousAt (closedBall_mem_nhds _ (by positivity))
  let η := w y s / 2
  have hη : 0 < η := half_pos hwpos
  have hηw : η < w y s := half_lt_self hwpos
  obtain ⟨ρ, hρ, hρw⟩ := nhds_basis_closedBall.mem_iff.mp
    (hstart (Ioi_mem_nhds hηw))
  let R := min ρ (r / 2)
  have hR : 0 < R := lt_min hρ (half_pos hr)
  have hRρ : R ≤ ρ := min_le_left _ _
  have hRr : R ≤ r / 2 := min_le_right _ _
  let δ := C + (6 * (A + R * (‖v‖ + B)) + 24 * θ) ^ 2 / (4 * (24 * θ) * R ^ 2)
  have hcompare := lower_bound_on_moving_halfBall
    (δ := δ) (A := A) (B := B) (C := C)
    hR (hRr.trans (half_le_self hr.le)) hst hθ hη.le v htravel le_rfl a b c ha hell
    (fun x hx q hq ↦ (le_abs_self _).trans
      (hA (x, q) ⟨ball_subset_closedBall hx, hq.1.le, hq.2.le⟩))
    (fun x hx q hq ↦ hB (x, q) ⟨ball_subset_closedBall hx, hq.1.le, hq.2.le⟩)
    hc
    (fun x hx q hq ↦ (le_abs_self _).trans
      (hC (x, q) ⟨ball_subset_closedBall hx, hq.1.le, hq.2.le⟩))
    w hwcont hwspace hwtime hwsuper hwnonneg
    (fun x hx ↦ (hρw ((closedBall_subset_closedBall hRρ) hx)).le)
  exact (mul_pos (div_pos hη (by norm_num : (0 : ℝ) < 8)) (Real.exp_pos _)).trans_le
    (hcompare t ⟨hst.le, le_rfl⟩ (y + (t - s) • v)
      (mem_closedBall_self (half_pos hR).le))

end ParabolicMaximum
