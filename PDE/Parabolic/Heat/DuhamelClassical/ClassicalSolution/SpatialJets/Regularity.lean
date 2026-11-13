/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.DuhamelClassical.ClassicalSolution.SpatialJets.SpatialDerivatives
public import PDE.Parabolic.Heat.DuhamelClassical.ClassicalSolution.SpatialJets.TimeDerivative
import PDE.Parabolic.Heat.Duhamel.JointContinuity
import PDE.Analysis.Calculus.SpaceTime.Regularity

/-!
# Classical regularity from continuous spatial source derivatives

The derivative formulas give `C²` spatial slices and joint `C¹` regularity at positive
time. Their common convolution term cancels to give the forced heat equation.
-/

@[expose] public section

open Set MeasureTheory Filter PDE.Common
open scoped Interval Topology

namespace HeatEquation

variable {n : ℕ}

/-- Continuous bounded first spatial derivatives of the source give a continuously differentiable
Duhamel spatial slice. -/
theorem contDiff_one_integral_initialValueSolution_space
    (g : ℝ → ℝ^n → ℝ) (hg : Continuous (Function.uncurry g))
    (hg1 : ∀ s, ContDiff ℝ 1 (g s)) (hgc : ∀ s, HasCompactSupport (g s))
    {M : ℝ} (hbound : ∀ s x, ‖g s x‖ ≤ M)
    (hpartial : ∀ i : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (g p.1)) p.2))
    (C : Fin n → ℝ) (hC : ∀ i s x, ‖(∂[i] (g s)) x‖ ≤ C i)
    (t : ℝ) :
    ContDiff ℝ 1 (fun z ↦ ∫ s in 0..t, initialValueSolution (g s) z (t - s)) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨_, ?_, fun x ↦ hasFDerivAt_integral_initialValueSolution_space_sum
    g hg hg1 hgc hbound hpartial C hC x t⟩
  apply continuous_finsetSum
  intro i _
  exact ((continuous_integral_initialValueSolution_family
    (fun s ↦ (∂[i] (g s))) (hpartial i) (hC i)).comp
      (continuous_id.prodMk continuous_const)).smul continuous_const

/-- Continuous bounded mixed second spatial derivatives of the source give a twice continuously
differentiable Duhamel spatial slice. -/
theorem contDiff_two_integral_initialValueSolution_space
    (g : ℝ → ℝ^n → ℝ) (hg : Continuous (Function.uncurry g))
    (hg2 : ∀ s, ContDiff ℝ 2 (g s)) (hgc : ∀ s, HasCompactSupport (g s))
    {M : ℝ} (hbound : ∀ s x, ‖g s x‖ ≤ M)
    (hpartial : ∀ i : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (g p.1)) p.2))
    (C : Fin n → ℝ) (hC : ∀ i s x, ‖(∂[i] (g s)) x‖ ≤ C i)
    (hsecond : ∀ i j : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (∂[j] (g p.1))) p.2))
    (B : Fin n → Fin n → ℝ)
    (hB : ∀ i j s x, ‖(∂[i] (∂[j] (g s))) x‖ ≤ B i j)
    (t : ℝ) :
    ContDiff ℝ 2 (fun z ↦ ∫ s in 0..t, initialValueSolution (g s) z (t - s)) := by
  have hg1 (s : ℝ) : ContDiff ℝ 1 (g s) := (hg2 s).of_le (by norm_num)
  apply contDiff_succ_iff_hasFDerivAt.mpr
  refine ⟨_, ?_, fun x ↦ hasFDerivAt_integral_initialValueSolution_space_sum
    g hg hg1 hgc hbound hpartial C hC x t⟩
  apply ContDiff.sum
  intro j _
  exact (contDiff_one_integral_initialValueSolution_space
    (fun s ↦ (∂[j] (g s))) (hpartial j)
    (fun s ↦ PDE.contDiff_partialDeriv_of_succ (hg2 s))
    (fun s ↦ (hgc s).fderiv_apply ℝ (EuclideanSpace.single j 1))
    (hC j) (fun i ↦ hsecond i j) (fun i ↦ B i j) (fun i ↦ hB i j) t).smul contDiff_const

/-- The mixed second derivatives of the Duhamel integral vary continuously in space and
time. -/
theorem continuous_secondPartial_integral_initialValueSolution
    (g : ℝ → ℝ^n → ℝ) (hg : Continuous (Function.uncurry g))
    (hg2 : ∀ s, ContDiff ℝ 2 (g s)) (hgc : ∀ s, HasCompactSupport (g s))
    {M : ℝ} (hbound : ∀ s x, ‖g s x‖ ≤ M)
    (hpartial : ∀ i : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (g p.1)) p.2))
    (C : Fin n → ℝ) (hC : ∀ i s x, ‖(∂[i] (g s)) x‖ ≤ C i)
    (hsecond : ∀ i j : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (∂[j] (g p.1))) p.2))
    (B : Fin n → Fin n → ℝ)
    (hB : ∀ i j s x, ‖(∂[i] (∂[j] (g s))) x‖ ≤ B i j)
    (i j : Fin n) :
    Continuous (fun p : ℝ^n × ℝ ↦ (∂[i] (∂[j]
      (fun z ↦ ∫ s in 0..p.2, initialValueSolution (g s) z (p.2 - s)))) p.1) := by
  simp_rw [secondPartial_integral_initialValueSolution_eq_source
    g hg hg2 hgc hbound hpartial C hC hsecond B hB]
  exact continuous_integral_initialValueSolution_family
    (fun s ↦ (∂[i] (∂[j] (g s)))) (hsecond i j) (hB i j)

/-- The separate spatial and time derivative formulas assemble into joint continuous
differentiability at positive time. -/
theorem contDiffOn_one_integral_initialValueSolution
    (g : ℝ → ℝ^n → ℝ) (hg : Continuous (Function.uncurry g))
    (hg2 : ∀ s, ContDiff ℝ 2 (g s)) (hgc : ∀ s, HasCompactSupport (g s))
    {M : ℝ} (hbound : ∀ s x, ‖g s x‖ ≤ M)
    (hpartial : ∀ i : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (g p.1)) p.2))
    (C : Fin n → ℝ) (hC : ∀ i s x, ‖(∂[i] (g s)) x‖ ≤ C i)
    (hsecond : ∀ i : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (∂[i] (g p.1))) p.2))
    (B : Fin n → ℝ)
    (hB : ∀ i s x, ‖(∂[i] (∂[i] (g s))) x‖ ≤ B i) :
    ContDiffOn ℝ 1 (fun p : ℝ^n × ℝ ↦
      ∫ s in 0..p.2, initialValueSolution (g s) p.1 (p.2 - s))
      (univ ×ˢ Ioi 0) := by
  let Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ := fun p ↦
    ∑ i : Fin n,
      (∫ s in 0..p.2, initialValueSolution (∂[i] (g s)) p.1 (p.2 - s)) •
        (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)
  let Dt : ℝ^n × ℝ → ℝ := fun p ↦ g p.2 p.1 +
    ∑ i : Fin n, ∫ s in 0..p.2,
      initialValueSolution (∂[i] (∂[i] (g s))) p.1 (p.2 - s)
  have hDx : Continuous Dx := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_integral_initialValueSolution_family
      (fun s ↦ (∂[i] (g s))) (hpartial i) (hC i)).smul continuous_const
  have hDt : Continuous Dt := by
    apply (hg.comp continuous_swap).add
    apply continuous_finsetSum
    intro i _
    exact continuous_integral_initialValueSolution_family
      (fun s ↦ (∂[i] (∂[i] (g s)))) (hsecond i) (hB i)
  simpa only [interior_Ioi, Function.uncurry_def] using
    PDE.Analysis.contDiffOn_one_of_space_time_derivatives
      (u := fun x t ↦ ∫ s in 0..t, initialValueSolution (g s) x (t - s))
      (Ω := univ) (I := Ioi 0)
      isOpen_univ hDx.continuousOn hDt.continuousOn
      (fun p _ ↦ hasFDerivAt_integral_initialValueSolution_space_sum
        g hg (fun s ↦ (hg2 s).of_le (by norm_num)) hgc hbound hpartial C hC p.1 p.2)
      (fun p hp ↦
        (hasDerivAt_integral_initialValueSolution_of_spatial_jets_sum
          g hg hg2 hgc hbound hsecond B hB p.1 p.2 hp.2).hasDerivWithinAt)

/-- The time derivative and spatial Laplacian cancel their common convolution term, leaving the
source. -/
theorem integral_initialValueSolution_forced_heat_residual
    (g : ℝ → ℝ^n → ℝ) (hg : Continuous (Function.uncurry g))
    (hg2 : ∀ s, ContDiff ℝ 2 (g s)) (hgc : ∀ s, HasCompactSupport (g s))
    {M : ℝ} (hbound : ∀ s x, ‖g s x‖ ≤ M)
    (hpartial : ∀ i : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (g p.1)) p.2))
    (C : Fin n → ℝ) (hC : ∀ i s x, ‖(∂[i] (g s)) x‖ ≤ C i)
    (hsecond : ∀ i j : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (∂[j] (g p.1))) p.2))
    (B : Fin n → Fin n → ℝ)
    (hB : ∀ i j s x, ‖(∂[i] (∂[j] (g s))) x‖ ≤ B i j)
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    deriv (fun τ ↦ ∫ s in 0..τ, initialValueSolution (g s) x (τ - s)) t -
      (∑ i : Fin n, (∂[i] (∂[i]
        (fun z ↦ ∫ s in 0..t, initialValueSolution (g s) z (t - s)))) x) = g t x := by
  rw [(hasDerivAt_integral_initialValueSolution_of_spatial_jets_sum
    g hg hg2 hgc hbound (fun i ↦ hsecond i i) (fun i ↦ B i i)
      (fun i ↦ hB i i) x t ht).deriv]
  simp_rw [secondPartial_integral_initialValueSolution_eq_source
    g hg hg2 hgc hbound hpartial C hC hsecond B hB]
  exact add_sub_cancel_right _ _

end HeatEquation
