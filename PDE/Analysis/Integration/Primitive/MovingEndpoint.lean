/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ParametricIntervalSmooth.ClosedDomain
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Joint smoothness with moving integration endpoints

Affine reparametrization sends each oriented integration interval to the unit
interval, even when its length changes sign or vanishes. Relative parameter
integration then gives smoothness up to the endpoints of a closed time strip.
Only values and derivatives on the strip enter the hypotheses.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff Interval Topology

namespace PDE.Analysis

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {S U : Set X} {a b c : ℝ} {n : ℕ∞}

/-- Two smooth moving endpoints in a fixed closed interval give a smooth
oriented integral on a closed convex parameter domain. Their order may change. -/
theorem contDiffOn_intervalIntegral_variable_bounds
    (hS : IsClosed S) (hconv : Convex ℝ S) (hne : (interior S).Nonempty)
    {H : X × ℝ → Y} {α β : X → ℝ}
    (hH : ContDiffOn ℝ n H (S ×ˢ uIcc a b))
    (hα : ContDiffOn ℝ n α S) (hβ : ContDiffOn ℝ n β S)
    (hαmem : MapsTo α S (uIcc a b)) (hβmem : MapsTo β S (uIcc a b)) :
    ContDiffOn ℝ n (fun x ↦ ∫ t in α x..β x, H (x, t)) S := by
  have hαfst : ContDiffOn ℝ n (fun p : X × ℝ ↦ α p.1) (S ×ˢ uIcc (0 : ℝ) 1) :=
    hα.comp contDiffOn_fst (fun _ hp ↦ hp.1)
  have hβfst : ContDiffOn ℝ n (fun p : X × ℝ ↦ β p.1) (S ×ˢ uIcc (0 : ℝ) 1) :=
    hβ.comp contDiffOn_fst (fun _ hp ↦ hp.1)
  have hG : ContDiffOn ℝ n (fun p : X × ℝ ↦
      (β p.1 - α p.1) • H (p.1, α p.1 + (β p.1 - α p.1) * p.2))
      (S ×ˢ uIcc (0 : ℝ) 1) := by
    apply (hβfst.sub hαfst).smul
    apply hH.comp
      (contDiffOn_fst.prodMk (hαfst.add ((hβfst.sub hαfst).mul contDiffOn_snd)))
    intro p hp
    refine ⟨hp.1, ?_⟩
    simpa only [smul_eq_mul, mul_comm] using
      (convex_uIcc a b : Convex ℝ (uIcc a b)).add_smul_sub_mem
        (hαmem hp.1) (hβmem hp.1)
        (by simpa using hp.2)
  apply (contDiffOn_intervalIntegral_closed hS hconv hne hG).congr
  intro x _
  dsimp only
  rw [intervalIntegral.integral_smul]
  simpa using (intervalIntegral.smul_integral_comp_add_mul
    (fun t ↦ H (x, t)) (a := 0) (b := 1) (β x - α x) (α x)).symm

/-- A jointly smooth integrand on an open parameter domain times a closed
interval has a jointly smooth moving upper primitive relative to that same
strip. Both time boundaries are included, and the anchor can be anywhere in
the interval. Neither a smooth extension nor ordered endpoints are assumed. -/
theorem contDiffOn_intervalIntegral_moving_upper
    (hU : IsOpen U) {H : X × ℝ → Y}
    (hH : ContDiffOn ℝ n H (U ×ˢ uIcc a b)) (hc : c ∈ uIcc a b) :
    ContDiffOn ℝ n (fun p : X × ℝ ↦ ∫ t in c..p.2, H (p.1, t))
      (U ×ˢ uIcc a b) := by
  by_cases hab : a = b
  · subst b
    simp only [uIcc_self, mem_singleton_iff] at hc
    subst c
    apply (contDiffOn_const (c := (0 : Y))).congr
    intro p hp
    simp only [mem_prod, uIcc_self, mem_singleton_iff] at hp
    simp [hp.2]
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let S := closedBall x r ×ˢ uIcc a b
  have hS : IsClosed S := isClosed_closedBall.prod isClosed_Icc
  have hconv : Convex ℝ S := (convex_closedBall x r).prod (convex_uIcc a b)
  have hne : (interior S).Nonempty := by
    rw [interior_prod_eq]
    exact ⟨⟨x, (min a b + max a b) / 2⟩,
      ball_subset_interior_closedBall (mem_ball_self hr),
      by
        rw [uIcc, interior_Icc]
        exact ⟨left_lt_add_div_two.mpr (min_lt_max.mpr hab),
          add_div_two_lt_right.mpr (min_lt_max.mpr hab)⟩⟩
  have hi : ContDiffOn ℝ n (fun p : X × ℝ ↦ ∫ s in c..p.2, H (p.1, s)) S :=
    contDiffOn_intervalIntegral_variable_bounds hS hconv hne
      (hH.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd)
        (fun p hp ↦ ⟨hrU hp.1.1, hp.2⟩))
      contDiffOn_const contDiffOn_snd (fun _ _ ↦ hc) (fun _ hp ↦ hp.2)
  apply (hi (x, t) ⟨mem_closedBall_self hr.le, ht⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    (continuous_fst.tendsto (x, t)).mono_left nhdsWithin_le_nhds
      (closedBall_mem_nhds x hr)] with p hp hpr
  exact ⟨hpr, hp.2⟩

end PDE.Analysis
