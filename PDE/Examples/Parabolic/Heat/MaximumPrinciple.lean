/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.MaximumPrinciple.Boundary
public import PDE.Parabolic.Heat.MaximumPrinciple.Positivity
import PDE.FDeriv.Euclidean.Laplacian
import CAS.ExactTactic

/-!
# Heat principles from derivatives within the time interval

The polynomial example solves the ordinary equation `uₜ = Δu` with the time
derivative taken within `(0,T]`, so no value after `T` enters the argument.
It is a nonconstant caloric polynomial up to time `T`, then abruptly becomes
zero. Its later discontinuity does not prevent the principles from applying on
the original cylinder.
-/

@[expose] public section

noncomputable section

namespace PDE.Examples.HeatMaximumPrinciple

open HeatEquation ParabolicMaximum Set
open scoped ContDiff

/-- A caloric polynomial on the original interval, with an arbitrary jump after it. -/
def terminalHeat {n : ℕ} (T : ℝ) (x : ℝ^n) (t : ℝ) : ℝ :=
  if t ≤ T then 1 + ‖x‖ ^ 2 + 2 * (n : ℝ) * t else 0

/-- Each spatial slice is smooth: the same quadratic polynomial before the cutoff, zero after
it. -/
theorem terminalHeat_contDiff_space {n : ℕ} {T t : ℝ} :
    ContDiff ℝ ∞ (fun x : ℝ^n ↦ terminalHeat T x t) := by
  by_cases ht : t ≤ T
  · simpa only [terminalHeat, ite_eq_left ht] using
      (contDiff_const.add (contDiff_norm_sq ℝ)).add contDiff_const
  · simpa only [terminalHeat, ite_eq_right ht] using contDiff_const

/-- The spatial Laplacian is exactly the time slope, including at the final time. -/
theorem terminalHeat_laplacian {n : ℕ} {T t : ℝ} (ht : t ≤ T) (x : ℝ^n) :
    laplacian (fun y ↦ terminalHeat T y t) x = 2 * (n : ℝ) := by
  simp only [terminalHeat, ite_eq_left ht]
  rw [laplacian_add _ _ x
      (contDiffAt_const.add (contDiff_norm_sq ℝ).contDiffAt) contDiffAt_const,
    laplacian_add _ _ x contDiffAt_const (contDiff_norm_sq ℝ).contDiffAt]
  simp

/-- The polynomial solves the heat equation with within-time derivatives,
even where the total representative has a jump immediately afterwards. -/
theorem terminalHeat_hasDerivWithinAt {n : ℕ} {T t : ℝ}
    (ht : t ∈ Ioc 0 T) (x : ℝ^n) :
    HasDerivWithinAt (terminalHeat T x)
      (laplacian (fun y ↦ terminalHeat T y t) x) (Ioc 0 T) t := by
  rw [terminalHeat_laplacian ht.2]
  have hpoly : HasDerivAt (fun s : ℝ ↦ 1 + ‖x‖ ^ 2 + 2 * (n : ℝ) * s)
      (2 * (n : ℝ)) t := by
    cas
  exact hpoly.hasDerivWithinAt.congr_of_mem
    (fun s hs ↦ by simp only [terminalHeat, ite_eq_left hs.2]) ht

/-- Continuity on the closed cylinder ignores the chosen values after its final time. -/
theorem terminalHeat_continuousOn {n : ℕ} (U : Set (ℝ^n)) (T : ℝ) :
    ContinuousOn (fun p : ℝ^n × ℝ ↦ terminalHeat T p.1 p.2) (closedCylinder U T) := by
  have hpoly : Continuous (fun p : ℝ^n × ℝ ↦ 1 + ‖p.1‖ ^ 2 + 2 * (n : ℝ) * p.2) :=
    (continuous_const.add (continuous_fst.norm.pow 2)).add
      (continuous_const.mul continuous_snd)
  apply hpoly.continuousOn.congr
  intro p hp
  simp only [terminalHeat, ite_eq_left hp.2.2]

/-- Both attained-extremum conclusions apply to this nonconstant heat field. -/
theorem terminalHeat_boundary_extrema {n : ℕ}
    {U : Set (ℝ^n)} {T : ℝ}
    (hU : IsOpen U) (hne : U.Nonempty) (hcompact : IsCompact (closure U)) (hT : 0 < T) :
    (∃ p ∈ parabolicBoundary U T,
      IsMaxOn (fun q : ℝ^n × ℝ ↦ terminalHeat T q.1 q.2) (closedCylinder U T) p) ∧
    (∃ p ∈ parabolicBoundary U T,
      IsMinOn (fun q : ℝ^n × ℝ ↦ terminalHeat T q.1 q.2) (closedCylinder U T) p) := by
  have hd (x : ℝ^n) (t : ℝ) (ht : t ∈ Ioo 0 T) :=
    (terminalHeat_hasDerivWithinAt ⟨ht.1, ht.2.le⟩ x).hasDerivAt
      (Ioc_mem_nhds ht.1 ht.2)
  have heq (x : ℝ^n) (t : ℝ) (ht : t ∈ Ioo 0 T) :
      heatParabolicOperator (terminalHeat T) x t = 0 := by
    rw [heatParabolicOperator, (hd x t ht).deriv, sub_self]
  have hspace : ∀ x ∈ U, ∀ t ∈ Ioo 0 T,
      ContDiffAt ℝ 2 (fun y ↦ terminalHeat T y t) x :=
    fun _ _ _ ht ↦ terminalHeat_contDiff_space.of_le (by norm_num) |>.contDiffAt
  exact ⟨exists_isMaxOn_parabolicBoundary hU hne hcompact hT
    (terminalHeat_continuousOn U T) hspace
    (fun x _ t ht ↦ (hd x t ht).differentiableAt)
    (fun x _ t ht ↦ (heq x t ht).le),
    exists_isMinOn_parabolicBoundary hU hne hcompact hT
      (terminalHeat_continuousOn U T) hspace
      (fun x _ t ht ↦ (hd x t ht).differentiableAt)
      (fun x _ t ht ↦ (heq x t ht).ge)⟩

/-- For `T = 1`, the representative at `x = 0` is discontinuous in time at `t = 1`. -/
theorem terminalHeat_not_continuousAt :
    ¬ ContinuousAt (terminalHeat (n := 1) 1 0) 1 := by
  intro h
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp h 1 (by norm_num)
  have hd : dist (1 + δ / 2) (1 : ℝ) < δ := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
    linarith
  have hgt : ¬1 + δ / 2 ≤ (1 : ℝ) := by linarith
  have hc := hclose hd
  norm_num [terminalHeat, hgt, Real.dist_eq] at hc

end PDE.Examples.HeatMaximumPrinciple
