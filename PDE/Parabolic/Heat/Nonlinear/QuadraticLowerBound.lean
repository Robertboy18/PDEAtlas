/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Nonlinear.DirichletMoment
import PDE.Elliptic.Classical.Harmonic.WeakMaximumPrinciple

/-!
# A universal lower bound for the quadratic heat equation

At an interior maximum of `-t * u` above one, the heat operator is both
nonnegative by the maximum principle and strictly negative by `uₜ - Δu = u²`.
Thus `t * u ≥ -1` on every closed strip starting from a finite initial slice.
Translating the strip to positive times removes any initial corner assumption.

The lower bound is singular at time zero.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE (laplacian)
open scoped Topology

namespace HeatEquation.Nonlinear

variable {n : ℕ} {Ω : Set (ℝ^n)} {u : ℝ → ℝ^n → ℝ}

/-- Quadratic absorption on the negative half-line gives `t * u(t,x) ≥ -1`,
independently of the initial size or sign, on a closed regular strip. -/
theorem IsInteriorDirichletSquareSolution.neg_one_le_time_mul
    {S T : ℝ} {g : ℝ^n → ℝ}
    (hu : IsInteriorDirichletSquareSolution Ω S g u)
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    (hT : 0 < T) (hTS : T < S) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ closure Ω, -1 ≤ t * u t x := by
  classical
  let v : ℝ^n → ℝ → ℝ := fun x t ↦ -t * u t x
  have htS {t : ℝ} (ht : t ∈ Ioc 0 T) : t ∈ Ioo 0 S :=
    ⟨ht.1, ht.2.trans_lt hTS⟩
  have hspace (x : ℝ^n) (hx : x ∈ Ω) (t : ℝ) (ht : t ∈ Ioc 0 T) :
      ContDiffAt ℝ 2 (fun y ↦ v y t) x :=
    contDiffAt_const.mul ((hu.space hΩ (htS ht)).contDiffAt (hΩ.mem_nhds hx))
  have hderiv (x : ℝ^n) (hx : x ∈ Ω) (t : ℝ) (ht : t ∈ Ioc 0 T) :
      HasDerivAt (v x) (-u t x + -t * deriv (fun r ↦ u r x) t) t := by
    convert ((hasDerivAt_id t).neg.fun_mul (hu.hasDerivAt hΩ hx (htS ht))) using 1 <;>
      simp only [v, Pi.neg_apply, id_eq, neg_one_mul]
  have hc : ContinuousOn (fun p : ℝ^n × ℝ ↦ v p.1 p.2)
      (ParabolicMaximum.closedCylinder Ω T) :=
    continuous_snd.neg.continuousOn.mul
      (hu.continuous.comp continuous_swap.continuousOn (fun q hq ↦
        ⟨⟨hq.2.1, hq.2.2.trans hTS.le⟩, hq.1⟩))
  let P : (ℝ^n → ℝ → ℝ) → ℝ^n → ℝ → ℝ := fun f x t ↦
    if 1 < f x t then heatParabolicOperator f x t else -1
  have h := ParabolicMaximum.strict_maximum_core hΩ hne hb.isCompact_closure hT
    P v hc (M := 1) (by
      intro x hx t ht hmax htime hlevel
      dsimp only [P]
      rw [ite_eq_left hlevel]
      have hd := htime.deriv_nonneg_of_left_lt ht.1 ht.2
        (hderiv x hx t ht).differentiableAt
      have hl := LaplacianEquation.laplacian_nonpos_at_localMax hmax (hspace x hx t ht)
      exact sub_nonneg.mpr (hl.trans hd)) (by
      intro x hx t ht
      dsimp only [P]
      split_ifs with hlevel
      · have heq := hu.equation t (htS ht) x hx
        change 1 < -t * u t x at hlevel
        have hu_neg : u t x < 0 := by nlinarith [ht.1]
        have hprod : 0 < (-u t x) * (-1 - t * u t x) :=
          mul_pos (neg_pos.mpr hu_neg) (by linarith)
        change deriv (v x) t - laplacian (fun y ↦ -t * u t y) x < 0
        rw [(hderiv x hx t ht).deriv, PDE.laplacian_const_smul]
        nlinarith
      · norm_num) (by
      intro q hq
      change -q.2 * u q.2 q.1 ≤ 1
      rcases hq with hq | hq
      · rw [hu.boundary_closed (hT.trans hTS) hq.1 ⟨hq.2.1, hq.2.2.trans hTS.le⟩, mul_zero]
        norm_num
      · rw [hq.2]
        norm_num)
  intro t ht x hx
  have hv : -t * u t x ≤ 1 := h (x, t) ⟨hx, ht⟩
  linarith

end HeatEquation.Nonlinear
