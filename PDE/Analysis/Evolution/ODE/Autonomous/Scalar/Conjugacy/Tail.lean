/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Autonomous.Scalar.Conjugacy
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import PDE.Analysis.Evolution.ODE.Autonomous.Scalar.Conjugacy.Tail.Basic

/-!
# Backward trajectories from the integral scalar conjugacy

A single smooth inverse chart gives backward trajectories for all sufficiently
small initial states of either sign. The exponential coordinate stays inside
that chart for every nonpositive time. The resulting trajectory solves the
nonlinear equation, including at time zero, and both its value and derivative
tend to zero at negative infinity.
-/

@[expose] public section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Analysis.Evolution.Scalar

private theorem exists_scalarConjugacy_chart
    {c r : ℝ} {b : ℝ → ℝ} (hr : 0 < r)
    (hb : ContDiffOn ℝ ∞ b (Ioo (-r) r))
    (hden : ∀ v ∈ Ioo (-r) r, 0 < c + v * b v) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      (e : ℝ → ℝ) = scalarConjugacy c b ∧
      0 ∈ e.source ∧ e.source ⊆ Ioo (-r) r ∧
      ContDiffOn ℝ ∞ (e.symm : ℝ → ℝ) e.target := by
  have hzero : (0 : ℝ) ∈ Ioo (-r) r := ⟨neg_lt_zero.mpr hr, hr⟩
  have hH := contDiffOn_scalarConjugacy hb hden
  have hH0 : ContDiffAt ℝ ∞ (scalarConjugacy c b) 0 :=
    hH.contDiffAt (isOpen_Ioo.mem_nhds hzero)
  have hd := (hasDerivAt_scalarConjugacy_zero hr hb.continuousOn hden).hasFDerivAt_equiv
    (one_ne_zero : (1 : ℝ) ≠ 0)
  let e₀ := hH0.toOpenPartialHomeomorph (scalarConjugacy c b) hd (by simp)
  let e := e₀.restrOpen (Ioo (-r) r) isOpen_Ioo
  have he : (e : ℝ → ℝ) = scalarConjugacy c b := rfl
  have he0 : (0 : ℝ) ∈ e.source := by
    change (0 : ℝ) ∈ e₀.source ∩ Ioo (-r) r
    exact ⟨hH0.mem_toOpenPartialHomeomorph_source hd (by simp), hzero⟩
  have hsub : e.source ⊆ Ioo (-r) r := by
    intro s hs
    change s ∈ e₀.source ∩ Ioo (-r) r at hs
    exact hs.2
  refine ⟨e, he, he0, hsub, ?_⟩
  intro y hy
  have hs := hsub (e.map_target hy)
  have hderiv : HasDerivAt (e : ℝ → ℝ)
      (deriv (scalarConjugacy c b) (e.symm y)) (e.symm y) := by
    rw [he]
    exact (hasDerivAt_scalarConjugacy hb.continuousOn hden hs).differentiableAt.hasDerivAt
  have hsmooth : ContDiffAt ℝ ∞ (e : ℝ → ℝ) (e.symm y) := by
    rw [he]
    exact hH.contDiffAt (isOpen_Ioo.mem_nhds hs)
  exact (e.contDiffAt_symm_deriv
    (ne_of_gt (deriv_scalarConjugacy_pos hb.continuousOn hden hs))
    hy hderiv hsmooth).contDiffWithinAt

/-- One inverse chart and one positive radius give exact backward trajectories
for every signed initial state in that radius. The denominator condition
implies `c > 0`. The trajectories stay between zero and their initial state,
are smooth near each nonpositive time, and have value and derivative tending to
zero at negative infinity. -/
theorem exists_scalarConjugacy_backward_tail
    {c r : ℝ} {b : ℝ → ℝ} (hr : 0 < r)
    (hb : ContDiffOn ℝ ∞ b (Ioo (-r) r))
    (hden : ∀ v ∈ Ioo (-r) r, 0 < c + v * b v) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ, ∃ δ : ℝ,
      0 < δ ∧ (e : ℝ → ℝ) = scalarConjugacy c b ∧
      0 ∈ e.source ∧ e.source ⊆ Ioo (-r) r ∧
      ContDiffOn ℝ ∞ (e.symm : ℝ → ℝ) e.target ∧
      Ioo (-δ) δ ⊆ e.source ∧
      ∀ s₀ ∈ Ioo (-δ) δ,
        let z : ℝ → ℝ := fun t ↦
          e.symm (Real.exp (c * t) * scalarConjugacy c b s₀)
        z 0 = s₀ ∧
        (∀ t ≤ 0,
          Real.exp (c * t) * scalarConjugacy c b s₀ ∈ e.target ∧
          z t ∈ Ioo (-r) r ∧ z t ∈ uIcc 0 s₀ ∧
          ContDiffAt ℝ ∞ z t ∧ HasDerivAt z (c * z t + (z t) ^ 2 * b (z t)) t) ∧
        Tendsto z atBot (𝓝 0) ∧ Tendsto (deriv z) atBot (𝓝 0) := by
  obtain ⟨e, he, heSource, hsource, hK⟩ := exists_scalarConjugacy_chart hr hb hden
  have he0 : e 0 = 0 := by
    rw [he, scalarConjugacy_zero]
  have heTarget : (0 : ℝ) ∈ e.target := by
    simpa only [he0] using e.map_source heSource
  obtain ⟨a, ha, haTarget⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds heTarget)
  have hball : Metric.ball (0 : ℝ) a ∈ 𝓝 (e 0) := by
    rw [he0]
    exact Metric.ball_mem_nhds (0 : ℝ) ha
  have hnear : e.source ∩ e ⁻¹' Metric.ball (0 : ℝ) a ∈ 𝓝 0 :=
    inter_mem (e.open_source.mem_nhds heSource)
      ((e.continuousAt heSource).preimage_mem_nhds hball)
  obtain ⟨δ, hδ, hδnear⟩ := Metric.mem_nhds_iff.mp hnear
  have hδball : Ioo (-δ) δ ⊆ Metric.ball (0 : ℝ) δ := by
    intro s hs
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using abs_lt.mpr hs
  have hδsource : Ioo (-δ) δ ⊆ e.source :=
    fun _ hs ↦ (hδnear (hδball hs)).1
  have hKball : ContDiffOn ℝ ∞ (e.symm : ℝ → ℝ) (Metric.ball 0 a) :=
    hK.mono haTarget
  have hKzero : e.symm 0 = 0 := by
    simpa only [he0] using e.left_inv heSource
  have hKsource : MapsTo (e.symm : ℝ → ℝ) (Metric.ball 0 a) (Ioo (-r) r) :=
    fun _ hy ↦ hsource (e.map_target (haTarget hy))
  have hKright : ∀ y ∈ Metric.ball 0 a, scalarConjugacy c b (e.symm y) = y := by
    intro y hy
    simpa only [he] using e.right_inv (haTarget hy)
  refine ⟨e, δ, hδ, he, heSource, hsource, hK, hδsource, ?_⟩
  intro s₀ hs₀
  have hsSmall : scalarConjugacy c b s₀ ∈ Metric.ball 0 a := by
    simpa only [mem_preimage, he] using (hδnear (hδball hs₀)).2
  have hKleft : e.symm (scalarConjugacy c b s₀) = s₀ := by
    simpa only [he] using e.left_inv (hδsource hs₀)
  have htail := scalarConjugacy_backward_tail_of_inverse
    (K := (e.symm : ℝ → ℝ)) hr ha hb.continuousOn hden
    hKball hKzero hKsource hKright hKleft hsSmall
  exact ⟨htail.1, fun t ht ↦
    ⟨haTarget (htail.2.1 t ht).1, (htail.2.1 t ht).2⟩, htail.2.2⟩

end PDE.Analysis.Evolution.Scalar
