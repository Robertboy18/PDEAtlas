/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import PDE.FDeriv.PartialDeriv
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Spatial evaluations along bounded weak trajectories

A family of scalar observations on a Banach space has bounded differentiated
evaluations whenever each observation is spatially differentiable. They are
pointwise limits of bounded difference quotients.

If every observation is C¹ and the spatial normed space is proper, uniform
boundedness on compact balls makes the original evaluations locally Lipschitz
in operator norm. Pairing these evaluations with a bounded weakly continuous
trajectory gives joint continuity.

For observations on `ℝ^n`, iterating the construction gives joint continuity
of every coordinate derivative word with one derivative to spare. The
dimension may be zero; no coordinate basis estimate or nontriviality
assumption is used.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Filter
open scoped Topology

/-- Differentiating a scalar observation in a fixed spatial direction gives a
bounded linear functional of its Banach-space argument. -/
def differentiatedEvaluation
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : E → X → ℝ) (ev : X → E →L[ℝ] ℝ)
    (hev : ∀ x U, ev x U = q U x) (v x : X)
    (hq : ∀ U, DifferentiableAt ℝ (q U) x) : E →L[ℝ] ℝ :=
  continuousLinearMapOfTendsto
    (l := 𝓝[≠] (0 : ℝ))
    (fun t ↦ t⁻¹ • (ev (x + t • v) - ev x))
    (f := fun U ↦ fderiv ℝ (q U) x v) <| tendsto_pi_nhds.mpr fun U ↦ by
      simpa only [smul_apply, sub_apply, hev] using
        ((hq U).hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero

/-- The differentiated evaluation is the directional Fréchet derivative. -/
@[simp] theorem differentiatedEvaluation_apply
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : E → X → ℝ) (ev : X → E →L[ℝ] ℝ)
    (hev : ∀ x U, ev x U = q U x) (v x : X)
    (hq : ∀ U, DifferentiableAt ℝ (q U) x) (U : E) :
    differentiatedEvaluation q ev hev v x hq U = fderiv ℝ (q U) x v :=
  rfl

/-- Pointwise C¹ spatial observations make their bounded evaluation functionals
continuous in operator norm. Properness supplies compact spatial balls;
completeness of the observation space supplies uniform boundedness. -/
theorem continuous_evaluation_of_contDiff
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
    (q : E → X → ℝ) (ev : X → E →L[ℝ] ℝ)
    (hev : ∀ x U, ev x U = q U x) (hq : ∀ U, ContDiff ℝ 1 (q U)) :
    Continuous ev := by
  rw [continuous_iff_continuousAt]
  intro x
  let K := Metric.closedBall x 1
  have hK : IsCompact K := isCompact_closedBall x 1
  let dev (v y : X) : E →L[ℝ] ℝ :=
    differentiatedEvaluation q ev hev v y
      (fun U ↦ (hq U).differentiable (by norm_num) |>.differentiableAt)
  have hb (U : E) : ∃ B : ℝ, ∀ z : K × {v : X // ‖v‖ = 1},
      ‖dev z.2 z.1 U‖ ≤ B := by
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
      ((hq U).continuous_fderiv (by norm_num)).continuousOn
    refine ⟨B, fun z ↦ ?_⟩
    change ‖(fderiv ℝ (q U) z.1) z.2‖ ≤ B
    calc
      _ ≤ ‖fderiv ℝ (q U) z.1‖ * ‖(z.2 : X)‖ :=
        (fderiv ℝ (q U) z.1).le_opNorm _
      _ = ‖fderiv ℝ (q U) z.1‖ := by rw [z.2.property, mul_one]
      _ ≤ B := hB z.1 z.1.property
  obtain ⟨B, hB⟩ := banach_steinhaus
    (g := fun z : K × {v : X // ‖v‖ = 1} ↦ dev z.2 z.1) hb
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hd (U : E) (y : X) (hy : y ∈ K) :
      ‖fderiv ℝ (q U) y‖ ≤ C * ‖U‖ := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (mul_nonneg hC (norm_nonneg U))
    intro v hv
    change ‖dev v y U‖ ≤ _
    exact (dev v y).le_opNorm U |>.trans
      (mul_le_mul_of_nonneg_right
        ((hB (⟨y, hy⟩, ⟨v, hv⟩)).trans (le_max_left _ _)) (norm_nonneg U))
  have hLip : LipschitzOnWith (Real.toNNReal C) ev K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal C hC]
    apply (ev y - ev z).opNorm_le_bound (mul_nonneg hC (norm_nonneg _))
    intro U
    change ‖ev y U - ev z U‖ ≤ _
    rw [hev, hev]
    calc
      _ ≤ (C * ‖U‖) * ‖y - z‖ :=
        (convex_closedBall x 1).norm_image_sub_le_of_norm_fderiv_le
          (fun a _ ↦ (hq U).differentiable (by norm_num) |>.differentiableAt)
          (fun a ha ↦ hd U a ha) hz hy
      _ = (C * ‖y - z‖) * ‖U‖ := by ring
  exact hLip.continuousOn.continuousAt (Metric.closedBall_mem_nhds x zero_lt_one)

/-- Operator-norm-continuous scalar evaluations are jointly continuous along a
bounded weakly continuous trajectory. The evaluation parameter and time may
be arbitrary topological spaces; the state space need not be complete. -/
theorem continuous_weak_evaluation
    {E T X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace T] [TopologicalSpace X]
    (ev : X → E →L[ℝ] ℝ) (hev : Continuous ev) (u : T → E) (B : ℝ)
    (hbound : ∀ t, ‖u t‖ ≤ B)
    (hweak : ∀ L : E →L[ℝ] ℝ, Continuous (fun t ↦ L (u t))) :
    Continuous (fun p : T × X ↦ ev p.2 (u p.1)) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hzero : Tendsto (fun z : T × X ↦
      ‖ev z.2 - ev p.2‖ * B + ‖ev p.2 (u z.1) - ev p.2 (u p.1)‖)
      (𝓝 p) (𝓝 0) := by
    have h₁ : ContinuousAt (fun z : T × X ↦ ‖ev z.2 - ev p.2‖ * B) p :=
      (((hev.comp continuous_snd).sub continuous_const).norm.mul_const B).continuousAt
    have h₂ : ContinuousAt (fun z : T × X ↦
        ‖ev p.2 (u z.1) - ev p.2 (u p.1)‖) p :=
      (((hweak (ev p.2)).comp continuous_fst).sub continuous_const).norm.continuousAt
    have h₁' : Tendsto (fun z : T × X ↦ ‖ev z.2 - ev p.2‖ * B)
        (𝓝 p) (𝓝 0) := by
      simpa only [ContinuousAt, sub_self, norm_zero, zero_mul] using h₁
    have h₂' : Tendsto (fun z : T × X ↦
        ‖ev p.2 (u z.1) - ev p.2 (u p.1)‖) (𝓝 p) (𝓝 0) := by
      simpa only [ContinuousAt, sub_self, norm_zero] using h₂
    simpa only [add_zero] using h₁'.add h₂'
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ ↦ norm_nonneg _) _ hzero
  intro z
  calc
    ‖ev z.2 (u z.1) - ev p.2 (u p.1)‖ ≤
        ‖ev z.2 (u z.1) - ev p.2 (u z.1)‖ +
          ‖ev p.2 (u z.1) - ev p.2 (u p.1)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖ev z.2 - ev p.2‖ * B + ‖ev p.2 (u z.1) - ev p.2 (u p.1)‖ := by
      apply add_le_add _ le_rfl
      exact ((ev z.2 - ev p.2).le_opNorm (u z.1)).trans
        (mul_le_mul_of_nonneg_left (hbound z.1) (norm_nonneg _))

/-- Every spatial derivative word within the supplied finite regularity is a
bounded linear evaluation of the Banach-space argument. -/
theorem exists_word_evaluation
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (q : E → ℝ^n → ℝ) (ev : ℝ^n → E →L[ℝ] ℝ)
    (hev : ∀ x U, ev x U = q U x) {k : ℕ} (hq : ∀ U, ContDiff ℝ k (q U))
    (α : List (Fin n)) (hα : α.length ≤ k) :
    ∃ L : ℝ^n → E →L[ℝ] ℝ, ∀ x U, L x U = iteratedPartialDeriv α (q U) x := by
  induction α with
  | nil => exact ⟨ev, hev⟩
  | cons i α ih =>
      obtain ⟨L, hL⟩ := ih (by simp only [List.length_cons] at hα; omega)
      have hreg (U : E) : ContDiff ℝ 1 (iteratedPartialDeriv α (q U)) := by
        apply (contDiff_iteratedPartialDeriv_of_le (hq U) α (by
          simp only [List.length_cons] at hα; omega)).of_le
        exact_mod_cast (show 1 ≤ k - α.length by simp only [List.length_cons] at hα; omega)
      exact ⟨fun x ↦ differentiatedEvaluation (fun U ↦ iteratedPartialDeriv α (q U))
        L hL (EuclideanSpace.single i 1) x
        (fun U ↦ (hreg U).differentiable (by norm_num) |>.differentiableAt),
        fun _ _ ↦ rfl⟩

/-- A derivative word with one spatial derivative to spare is jointly
continuous along every bounded weakly continuous Banach-space trajectory.
This includes dimension zero and the empty derivative word. -/
theorem continuous_word_of_weak_trajectory
    {n : ℕ} {E T : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace T]
    (q : E → ℝ^n → ℝ) (ev : ℝ^n → E →L[ℝ] ℝ)
    (hev : ∀ x U, ev x U = q U x) {k : ℕ} (hq : ∀ U, ContDiff ℝ k (q U))
    (α : List (Fin n)) (hα : α.length + 1 ≤ k) (u : T → E) (B : ℝ)
    (hbound : ∀ t, ‖u t‖ ≤ B)
    (hweak : ∀ L : E →L[ℝ] ℝ, Continuous (fun t ↦ L (u t))) :
    Continuous (fun p : T × ℝ^n ↦ iteratedPartialDeriv α (q (u p.1)) p.2) := by
  obtain ⟨L, hL⟩ := exists_word_evaluation q ev hev hq α (by omega)
  have hreg (U : E) : ContDiff ℝ 1 (iteratedPartialDeriv α (q U)) := by
    apply (contDiff_iteratedPartialDeriv_of_le (hq U) α (by omega)).of_le
    exact_mod_cast (show 1 ≤ k - α.length by omega)
  have hLc := continuous_evaluation_of_contDiff
    (fun U ↦ iteratedPartialDeriv α (q U)) L hL hreg
  simpa only [hL] using continuous_weak_evaluation L hLc u B hbound hweak

end PDE.Analysis
