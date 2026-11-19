/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.Parametric.Derivative
public import PDE.Analysis.Fourier.HilbertTransform.Velocity

/-!
# Joint continuity of compact Hilbert families

Fixed support and uniform Lipschitz and value bounds supply a common integrable
regularized kernel. Dominated convergence transfers joint continuity of the
input family to its principal value and its normalized velocity.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace PDE.Analysis

/-- The Hilbert transform preserves joint continuity of a family with fixed
support and common Lipschitz and value bounds. The parameter needs no derivative. -/
theorem continuous_hilbertPV_of_uniform_bounds
    {ι : Type*} [TopologicalSpace ι] [FirstCountableTopology ι]
    {q : ι → ℝ → ℝ} {K : ℝ≥0} {B L : ℝ}
    (hL : 0 ≤ L) (hq : ∀ t, LipschitzWith K (q t))
    (hB : ∀ t y, ‖q t y‖ ≤ B)
    (hs : ∀ t y, L ≤ |y| → q t y = 0)
    (hcont : Continuous (fun z : ℝ × ι ↦ q z.2 z.1)) :
    Continuous (fun z : ℝ × ι ↦ hilbertPV (q z.2) z.1) := by
  have hc (t : ι) : HasCompactSupport (q t) := by
    apply HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc
    intro y hy
    exact hs t y (le_of_not_ge fun h ↦ hy (abs_le.mp h))
  have hi (z : ℝ × ι) :=
    integrable_hilbertRegularizedKernel_one_of_lipschitzWith (hq z.2) (hc z.2) z.1
  have he (z : ℝ × ι) : hilbertPV (q z.2) z.1 =
      Real.pi⁻¹ * ∫ y, hilbertRegularizedKernel (q z.2) z.1 1 y :=
    (hasHilbertPV_of_regularized (hi z)).hilbertPV_eq
  simp_rw [he]
  apply continuous_iff_continuousAt.mpr
  intro z
  apply ContinuousAt.const_mul
  obtain ⟨bound, hb, hbound⟩ :=
    exists_integrable_hilbert_kernel_bound hL hq hB hs z.1
  apply continuousAt_of_dominated (bound := bound)
  · exact Eventually.of_forall fun p ↦ (hi p).aestronglyMeasurable
  · filter_upwards [continuous_fst.continuousAt
      (Metric.ball_mem_nhds z.1 zero_lt_one)] with p hp
    exact Eventually.of_forall (hbound p.2 p.1 hp)
  · exact hb
  · apply Eventually.of_forall
    intro y
    have hshift : Continuous (fun p : ℝ × ι ↦ q p.2 (p.1 - y)) :=
      hcont.comp ((continuous_fst.sub continuous_const).prodMk continuous_snd)
    unfold hilbertRegularizedKernel
    by_cases hy : |y| < 1
    · simp only [indicator_of_mem (s := {y : ℝ | |y| < 1}) hy]
      exact (hshift.sub hcont).continuousAt.div_const y
    · simp only [indicator_of_notMem (s := {y : ℝ | |y| < 1}) hy, sub_zero]
      exact hshift.continuousAt.div_const y

/-- Joint continuity of a principal-value family gives joint continuity of its
velocity normalized at zero, by continuity of the parametric primitive. -/
theorem continuous_hilbertPVVelocity_of_continuous_hilbertPV
    {ι : Type*} [TopologicalSpace ι] {q : ι → ℝ → ℝ}
    (hcont : Continuous (fun z : ℝ × ι ↦ hilbertPV (q z.2) z.1)) :
    Continuous (fun z : ℝ × ι ↦ hilbertPVVelocity (q z.2) z.1) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (a₀ := 0) (f := fun z : ℝ × ι ↦ hilbertPV (q z.2)) _ continuous_fst
  exact hcont.comp (continuous_snd.prodMk continuous_fst.snd)

end PDE.Analysis
