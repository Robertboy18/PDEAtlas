/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.MaximumPrinciple
import Mathlib.Analysis.Calculus.Deriv.Add
import PDE.Elliptic.Classical.Harmonic.WeakMaximumPrinciple
import PDE.FDeriv.Calculus

/-!
# Weighted comparison with singular absorption barriers

A weight vanishing on the boundary permits comparison with a singular barrier.
At a positive maximum of the weighted difference, a member of the barrier family
touches the subsolution at a positive time and an interior point.
-/

@[expose] public noncomputable section

open Filter Set
open PDE (laplacian)
open ParabolicMaximum
open scoped Topology

namespace HeatEquation.Nonlinear

/-- A singular family of strict absorption supersolutions bounds a subsolution
with nonpositive initial values. No order on the lateral values of `v` is needed:
the continuous weight vanishes there. -/
theorem weighted_quadratic_absorption_le
    {n : ℕ} {Ω : Set (ℝ^n)} {T a : ℝ} {v : ℝ^n → ℝ → ℝ}
    {p : ℝ^n → ℝ} {B : ℝ → ℝ^n → ℝ → ℝ}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hk : IsCompact (closure Ω)) (hT : 0 < T)
    (ha : 0 ≤ a) (hpc : ContinuousOn p (closure Ω))
    (hp : ∀ x ∈ Ω, 0 < p x) (hp0 : ∀ x ∈ closure Ω, 0 ≤ p x)
    (hpbd : ∀ x ∈ frontier Ω, p x = 0)
    (hvc : ContinuousOn (fun q : ℝ^n × ℝ ↦ v q.1 q.2) (closedCylinder Ω T))
    (hvs : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, ContDiffAt ℝ 2 (fun y ↦ v y t) x)
    (hvt : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, DifferentiableAt ℝ (v x) t)
    (hv : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, heatParabolicOperator v x t ≤ -(v x t) ^ 2)
    (hv0 : ∀ x ∈ closure Ω, v x 0 ≤ 0)
    (hBrel : ∀ M > 0, ∀ x ∈ Ω, ∀ t ∈ Icc 0 T, p x * B M x t = a * t + M)
    (hBs : ∀ M > 0, ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ B M y t) x)
    (hBt : ∀ M > 0, ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, DifferentiableAt ℝ (B M x) t)
    (hB : ∀ M > 0, ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      0 < heatParabolicOperator (B M) x t + (B M x t) ^ 2) :
    ∀ q ∈ closedCylinder Ω T, p q.1 * v q.1 q.2 ≤ a * q.2 := by
  classical
  let Y : ℝ^n → ℝ → ℝ := fun x t ↦ p x * v x t - a * t
  let P : (ℝ^n → ℝ → ℝ) → ℝ^n → ℝ → ℝ := fun f x t ↦
    if 0 < f x t then
      heatParabolicOperator (fun y s ↦ v y s - B (f x t) y s) x t else -1
  have hcontact (x : ℝ^n) (hx : x ∈ Ω) (t : ℝ) (ht : t ∈ Ioc 0 T)
      (hlevel : 0 < Y x t) : v x t = B (Y x t) x t := by
    apply mul_left_cancel₀ (hp x hx).ne'
    have hr := hBrel (Y x t) hlevel x hx t (Ioc_subset_Icc_self ht)
    dsimp only [Y] at hr
    linarith
  have hYc : ContinuousOn (fun q : ℝ^n × ℝ ↦ Y q.1 q.2) (closedCylinder Ω T) :=
    ((hpc.comp continuous_fst.continuousOn (fun _ hq ↦ hq.1)).mul hvc).sub
      (continuous_const.mul continuous_snd).continuousOn
  have hop (M : ℝ) (hM : 0 < M) (x : ℝ^n) (hx : x ∈ Ω)
      (t : ℝ) (ht : t ∈ Ioc 0 T) :
      heatParabolicOperator (fun y s ↦ v y s - B M y s) x t =
        heatParabolicOperator v x t - heatParabolicOperator (B M) x t := by
    unfold heatParabolicOperator
    rw [deriv_fun_sub (hvt x hx t ht) (hBt M hM x hx t ht),
      PDE.laplacian_sub _ _ _ (hvs x hx t ht) (hBs M hM x hx t ht)]
    abel
  have h := strict_maximum_core hΩ hne hk hT P Y hYc (M := 0) (by
    intro x hx t ht hmax htime hlevel
    dsimp only [P]
    rw [ite_eq_left hlevel]
    have hc := hcontact x hx t ht hlevel
    have hle {y : ℝ^n} (hy : y ∈ Ω) {s : ℝ} (hs : s ∈ Icc 0 T) (hys : Y y s ≤ Y x t) :
        v y s - B (Y x t) y s ≤ v x t - B (Y x t) x t := by
      rw [hc, sub_self, sub_nonpos]
      refine le_of_mul_le_mul_left ?_ (hp y hy)
      rw [hBrel (Y x t) hlevel y hy s hs]
      dsimp only [Y] at hys
      linarith
    have hs : IsLocalMax (fun y ↦ v y t - B (Y x t) y t) x := by
      filter_upwards [hmax, hΩ.mem_nhds hx] with y hxy hy
      exact hle hy (Ioc_subset_Icc_self ht) hxy
    have htm : IsMaxOn (fun s ↦ v x s - B (Y x t) x s) (Icc 0 T) t :=
      fun s hs ↦ hle hx hs (htime hs)
    have hd := htm.deriv_nonneg_of_left_lt ht.1 ht.2
      ((hvt x hx t ht).sub (hBt (Y x t) hlevel x hx t ht))
    have hl := LaplacianEquation.laplacian_nonpos_at_localMax hs
      ((hvs x hx t ht).sub (hBs (Y x t) hlevel x hx t ht))
    exact sub_nonneg.mpr (hl.trans hd)) (by
    intro x hx t ht
    dsimp only [P]
    split_ifs with hlevel
    · rw [hop (Y x t) hlevel x hx t ht]
      have hc := hcontact x hx t ht hlevel
      have hvx := hv x hx t ht
      have hBx := hB (Y x t) hlevel x hx t ht
      rw [hc] at hvx
      linarith
    · norm_num) (by
    intro q hq
    rcases hq with hq | hq
    · dsimp only [Y]
      rw [hpbd q.1 hq.1, zero_mul, zero_sub]
      exact neg_nonpos.mpr (mul_nonneg ha hq.2.1)
    · have ht : q.2 = 0 := hq.2
      dsimp only [Y]
      rw [ht, mul_zero, sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (hp0 q.1 hq.1) (hv0 q.1 hq.1))
  intro q hq
  exact sub_nonpos.mp (h q hq)

end HeatEquation.Nonlinear
