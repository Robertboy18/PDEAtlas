/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Autonomous.Scalar.Conjugacy.Parameter.Inverse
import PDE.Analysis.Evolution.ODE.Autonomous.Scalar.Conjugacy.Tail.Basic

/-!
# Joint backward tails for the scalar integral conjugacy

One smooth inverse chart works for all nearby positive coefficients and all
sufficiently small signed initial states. Exponential contraction keeps the
inverse argument inside the same target interval at every nonpositive time.
The resulting family is jointly smooth in coefficient, initial state, and time,
solves the nonlinear equation, and converges with its time derivative to
the equilibrium at negative infinity.
-/

@[expose] public section

open Filter Metric Set
open scoped ContDiff Topology

namespace PDE.Analysis.Evolution.Scalar

/-- A single inverse and common positive radii give jointly smooth backward tails
for nearby coefficients and signed initial states. Each tail stays between zero
and its initial state, satisfies the nonlinear equation even at time zero, and
has value and time derivative tending to zero at negative infinity. -/
theorem exists_scalarConjugacy_joint_backward_tail
    {c0 : ℝ} {b : ℝ → ℝ} (hc0 : 0 < c0) (hb : ContDiff ℝ ∞ b) :
    ∃ K : ℝ × ℝ → ℝ, ∃ r ε δ : ℝ,
      0 < r ∧ 0 < ε ∧ 0 < δ ∧ δ ≤ r ∧
      ball c0 ε ⊆ Ioo (c0 / 2) (3 * c0 / 2) ∧
      (∀ c ∈ ball c0 ε, ∀ s ∈ Icc (-r) r, c0 / 4 < c + s * b s) ∧
      let z : (ℝ × ℝ) × ℝ → ℝ := fun p ↦
        K (p.1.1, Real.exp (p.1.1 * p.2) * scalarConjugacy p.1.1 b p.1.2)
      ContDiffOn ℝ ∞ z ((ball c0 ε ×ˢ ball 0 δ) ×ˢ Iic 0) ∧
      ∀ c ∈ ball c0 ε, ∀ s₀ ∈ ball 0 δ,
        let u : ℝ → ℝ := fun t ↦ z ((c, s₀), t)
        u 0 = s₀ ∧
        (∀ t ≤ 0, u t ∈ Ioo (-r) r ∧ u t ∈ uIcc 0 s₀ ∧
          ContDiffAt ℝ ∞ u t ∧ HasDerivAt u (c * u t + (u t) ^ 2 * b (u t)) t) ∧
        Tendsto u atBot (𝓝 0) ∧ Tendsto (deriv u) atBot (𝓝 0) := by
  obtain ⟨K, r, ε, η, δ₀, hr, hε, hη, hδ₀, hδ₀r, hwindow, hmargin,
    hK, hKzero, hright, hleft⟩ :=
    exists_contDiffOn_scalarConjugacy_joint_inverse hc0 hb
  obtain ⟨ρ, hρ, _, hHclosed⟩ := exists_pos_contDiffOn_scalarConjugacy_joint hc0 hb
  let δ : ℝ := min δ₀ ρ
  have hδ : 0 < δ := lt_min hδ₀ hρ
  have hδr : δ ≤ r := (min_le_left δ₀ ρ).trans hδ₀r
  have hsmall (s : ℝ) (hs : s ∈ ball 0 δ) : s ∈ ball 0 δ₀ :=
    ball_subset_ball (min_le_left δ₀ ρ) hs
  have habs (s : ℝ) (hs : s ∈ ball 0 δ) : |s| < δ := by
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hs
  have hquarter : (0 : ℝ) < c0 / 4 := by linarith only [hc0]
  have hden (c : ℝ) (hc : c ∈ ball c0 ε) :
      ∀ s ∈ Ioo (-r) r, 0 < c + s * b s := by
    intro s hs
    exact hquarter.trans (hmargin c hc s ⟨hs.1.le, hs.2.le⟩)
  have hHjoint : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ ↦ scalarConjugacy p.1 b p.2) (ball c0 ε ×ˢ ball 0 δ) := by
    apply hHclosed.mono
    intro p hp
    refine ⟨hwindow hp.1, ?_⟩
    exact abs_le.mp ((habs p.2 hp.2).trans_le (min_le_right δ₀ ρ)).le
  have hKslice (c : ℝ) (hc : c ∈ ball c0 ε) :
      ContDiffOn ℝ ∞ (fun y : ℝ ↦ K (c, y)) (ball 0 η) :=
    hK.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy ↦ ⟨hc, hy⟩)
  have htail (c : ℝ) (hc : c ∈ ball c0 ε) (s₀ : ℝ) (hs₀ : s₀ ∈ ball 0 δ) :
      let u : ℝ → ℝ := fun t ↦ K (c, Real.exp (c * t) * scalarConjugacy c b s₀)
      u 0 = s₀ ∧
      (∀ t ≤ 0,
        Real.exp (c * t) * scalarConjugacy c b s₀ ∈ ball 0 η ∧
        u t ∈ Ioo (-r) r ∧ u t ∈ uIcc 0 s₀ ∧
        ContDiffAt ℝ ∞ u t ∧ HasDerivAt u (c * u t + (u t) ^ 2 * b (u t)) t) ∧
      Tendsto u atBot (𝓝 0) ∧ Tendsto (deriv u) atBot (𝓝 0) :=
    scalarConjugacy_backward_tail_of_inverse hr hη hb.continuous.continuousOn
      (hden c hc) (hKslice c hc) (hKzero c hc)
      (fun y hy ↦ (hright c hc y hy).1) (fun y hy ↦ (hright c hc y hy).2)
      (hleft c hc s₀ (hsmall s₀ hs₀)).2 (hleft c hc s₀ (hsmall s₀ hs₀)).1
  have htarget (c : ℝ) (hc : c ∈ ball c0 ε)
      (s : ℝ) (hs : s ∈ ball 0 δ) (t : ℝ) (ht : t ≤ 0) :
      Real.exp (c * t) * scalarConjugacy c b s ∈ ball 0 η :=
    ((htail c hc s hs).2.1 t ht).1
  let D : Set ((ℝ × ℝ) × ℝ) := (ball c0 ε ×ˢ ball 0 δ) ×ˢ Iic 0
  let Y : (ℝ × ℝ) × ℝ → ℝ := fun p ↦
    Real.exp (p.1.1 * p.2) * scalarConjugacy p.1.1 b p.1.2
  let z : (ℝ × ℝ) × ℝ → ℝ := fun p ↦ K (p.1.1, Y p)
  have hHprojection : ContDiffOn ℝ ∞
      (fun p : (ℝ × ℝ) × ℝ ↦ scalarConjugacy p.1.1 b p.1.2) D :=
    hHjoint.comp contDiffOn_fst (fun _ hp ↦ hp.1)
  have hYjoint : ContDiffOn ℝ ∞ Y D :=
    (contDiffOn_fst.fst.mul contDiffOn_snd).exp.mul hHprojection
  have hzjoint : ContDiffOn ℝ ∞ z D :=
    hK.comp (contDiffOn_fst.fst.prodMk hYjoint)
      (fun p hp ↦ ⟨hp.1.1, htarget p.1.1 hp.1.1 p.1.2 hp.1.2 p.2 hp.2⟩)
  refine ⟨K, r, ε, δ, hr, hε, hδ, hδr, hwindow, hmargin, hzjoint, ?_⟩
  intro c hc s₀ hs₀
  have h := htail c hc s₀ hs₀
  exact ⟨h.1, fun t ht ↦ (h.2.1 t ht).2, h.2.2⟩

end PDE.Analysis.Evolution.Scalar
