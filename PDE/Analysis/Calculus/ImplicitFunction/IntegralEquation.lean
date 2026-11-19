/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Normalized integral equations in Banach spaces

A parameterized fixed-point equation whose right-hand side vanishes at zero
parameters has identity derivative in the unknown. Mathlib's implicit function
theorem then gives a solution and uniform balls for existence and uniqueness.
The same argument handles `w = a + t² K(N(w))` in a Banach space and
`w = a + t K(b * N(w))` in a Banach algebra, for every positive finite order.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace PDE.Analysis

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A fixed-point equation which vanishes at zero parameters has a small solution
of the same positive finite regularity, unique in a uniform ball of unknowns. -/
theorem exists_local_fixed_point_of_zero_parameter {k : ℕ} {F : P × E → E}
    (hF : ContDiff ℝ (k + 1) F) (hzero : ∀ w, F (0, w) = 0) :
    ∃ δ r : ℝ, 0 < δ ∧ 0 < r ∧
      ∃ ψ : P → E,
        ContDiffOn ℝ (k + 1) ψ (Metric.ball 0 δ) ∧
        (∀ p ∈ Metric.ball 0 δ, ‖ψ p‖ < r) ∧
        (∀ p ∈ Metric.ball 0 δ, ψ p = F (p, ψ p)) ∧
        (∀ p ∈ Metric.ball 0 δ, ∀ w, ‖w‖ < r → w = F (p, w) → ψ p = w) := by
  let G : P × E → E := fun p ↦ p.2 - F p
  have hG : ContDiff ℝ (k + 1) G := contDiff_snd.sub hF
  have hG0 : G (0, 0) = 0 := by simp [G, hzero]
  -- On the slice with zero parameters, the residual is the identity in the unknown.
  have hpartial : (fderiv ℝ G (0, 0)).comp
      (ContinuousLinearMap.inr ℝ P E) = ContinuousLinearMap.id ℝ E := by
    have hd := (hG.differentiable (by norm_cast) (0, 0)).hasFDerivAt.comp 0
      (ContinuousLinearMap.inr ℝ P E).hasFDerivAt
    have heq : G ∘ Prod.mk 0 = id := by
      funext w
      simp [G, hzero]
    rw [heq] at hd
    exact hd.unique (hasFDerivAt_id 0)
  have hinv : ((fderiv ℝ G (0, 0)).comp
      (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
    rw [hpartial]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  let ψ := hG.contDiffAt.implicitFunction (by simp : ((k + 1 : ℕ) : ℕ∞ω) ≠ 0) hinv
  have hψ : ContDiffAt ℝ (k + 1) ψ 0 :=
    hG.contDiffAt.contDiffAt_implicitFunction (by simp) hinv
  have hψ0 : ψ 0 = 0 := hG.contDiffAt.implicitFunction_apply_self (by simp) hinv
  have hunique : ∀ᶠ p in 𝓝 ((0 : P), (0 : E)), G p = 0 ↔ ψ p.1 = p.2 := by
    simpa only [hG0] using
      hG.contDiffAt.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.mp hunique
  have heq : ∀ᶠ p in 𝓝 (0 : P), G (p, ψ p) = 0 := by
    simpa only [hG0] using hG.contDiffAt.eventually_apply_implicitFunction
      (by simp) hinv
  have hsmall : ∀ᶠ p in 𝓝 (0 : P), ‖ψ p‖ < r := by
    simpa only [hψ0, dist_zero_right] using
      hψ.continuousAt.eventually (Metric.ball_mem_nhds (ψ 0) hr)
  have hreg := hψ.eventually (by simp : ((k + 1 : ℕ) : ℕ∞ω) ≠ ∞)
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (Metric.ball_mem_nhds (0 : P) hr) (hsmall.and (heq.and hreg)))
  refine ⟨δ, r, hδ, hr, ψ, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (hd hp).2.2.2.contDiffWithinAt
  · intro p hp
    exact (hd hp).2.1
  · intro p hp
    exact sub_eq_zero.mp (hd hp).2.2.1
  · intro p hp w hw he
    have hnear : (p, w) ∈ Metric.ball ((0 : P), (0 : E)) r := by
      simpa only [Metric.mem_ball, Prod.dist_eq, dist_zero_right, max_lt_iff] using
        And.intro (hd hp).1 hw
    exact (hru hnear).mp (sub_eq_zero.mpr he)

/-- The implicit function theorem constructs small solutions of the normalized
integral equation, with a uniform neighborhood of uniqueness. -/
theorem exists_local_integral_solution {k : ℕ} (K : E →L[ℝ] E) {N : E → E}
    (hN : ContDiff ℝ (k + 1) N) :
    ∃ δ r : ℝ, 0 < δ ∧ 0 < r ∧
      ∃ ψ : ℝ × E → E,
        ContDiffOn ℝ (k + 1) ψ (Metric.ball 0 δ) ∧
        (∀ p ∈ Metric.ball 0 δ, ‖ψ p‖ < r) ∧
        (∀ p ∈ Metric.ball 0 δ, ψ p = p.2 + p.1 ^ 2 • K (N (ψ p))) ∧
        (∀ p ∈ Metric.ball 0 δ, ∀ w, ‖w‖ < r →
          w = p.2 + p.1 ^ 2 • K (N w) → ψ p = w) := by
  apply exists_local_fixed_point_of_zero_parameter (F := fun p : (ℝ × E) × E ↦
    p.1.2 + p.1.1 ^ 2 • K (N p.2))
  · exact contDiff_fst.snd.add
      ((contDiff_fst.fst.pow 2).smul (K.contDiff.comp (hN.comp contDiff_snd)))
  · intro w
    simp

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- A reaction in a Banach algebra constructs a solution of the weighted integral
equation with the same positive finite regularity and uniform local uniqueness.
The coefficient is an independent parameter; no positive lower bound is needed. -/
theorem exists_local_weighted_integral_solution {k : ℕ} (K : A →L[ℝ] A) {N : A → A}
    (hN : ContDiff ℝ (k + 1) N) :
    ∃ δ r : ℝ, 0 < δ ∧ 0 < r ∧
      ∃ ψ : ℝ × (A × A) → A,
        ContDiffOn ℝ (k + 1) ψ (Metric.ball 0 δ) ∧
        (∀ p ∈ Metric.ball 0 δ, ‖ψ p‖ < r) ∧
        (∀ p ∈ Metric.ball 0 δ, ψ p = p.2.1 + p.1 • K (p.2.2 * N (ψ p))) ∧
        (∀ p ∈ Metric.ball 0 δ, ∀ w, ‖w‖ < r →
          w = p.2.1 + p.1 • K (p.2.2 * N w) → ψ p = w) := by
  apply exists_local_fixed_point_of_zero_parameter (F := fun p : (ℝ × (A × A)) × A ↦
    p.1.2.1 + p.1.1 • K (p.1.2.2 * N p.2))
  · exact contDiff_fst.snd.fst.add
      (contDiff_fst.fst.smul (K.contDiff.comp
        (contDiff_fst.snd.snd.mul (hN.comp contDiff_snd))))
  · intro w
    simp

end PDE.Analysis
