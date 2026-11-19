/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.DuhamelClassical.ClassicalSolution.SpatialJets.Regularity
public import PDE.Parabolic.Heat.Duhamel.Representation
import PDE.Analysis.Calculus.Support.Parametric
import PDE.FDeriv.PartialDeriv.Support.Parametric
import PDE.Parabolic.Heat.Duhamel.JointContinuity
import PDE.Parabolic.Heat.Duhamel.InitialTrace

/-!
# The forced heat equation for a forward-time source

The Duhamel formula uses only nonnegative source times. Clamping the time
parameter lets us reuse the integral regularity lemmas while allowing nonzero forcing
at the initial time. Joint compact support supplies all spatial derivative bounds.

This gives the regularity, equation and initial trace of Evans's theorem on the
nonhomogeneous heat problem in Chapter 2. Only spatial derivatives of the source enter
the proof.
-/

@[expose] public section

open PDE (laplacian)

open Set MeasureTheory Filter PDE.Common
open scoped Interval Topology

namespace HeatEquation

variable {n : ℕ}

/-- The Duhamel formula solves the forced heat equation with zero initial data for a compactly
supported forward-time source with continuous first and second spatial derivatives.

The source may be nonzero at time zero. The solution is jointly continuous through time zero,
has jointly continuous mixed second spatial derivatives, and is jointly `C¹` at positive time.
The initial trace is uniform in space. No time derivative of the source is assumed. -/
theorem nonhomogeneousSolution_regularity_of_forward_spatial_jets
    (f : ℝ^(n + 1) → ℝ)
    (hf : Continuous
      (fun p : Ici (0 : ℝ) × ℝ^n ↦ f (timeSpaceCons p.1 p.2)))
    (hf2 : ∀ s : ℝ, 0 ≤ s → ContDiff ℝ 2 (fun x ↦ f (timeSpaceCons s x)))
    (hfc : HasCompactSupport
      (fun p : Ici (0 : ℝ) × ℝ^n ↦ f (timeSpaceCons p.1 p.2)))
    (hfirst : ∀ i : Fin n, Continuous
      (fun p : Ici (0 : ℝ) × ℝ^n ↦
        (∂[i] (fun x ↦ f (timeSpaceCons p.1 x))) p.2))
    (hsecond : ∀ i j : Fin n, Continuous
      (fun p : Ici (0 : ℝ) × ℝ^n ↦
        (∂[i] (∂[j] (fun x ↦ f (timeSpaceCons p.1 x)))) p.2)) :
    Continuous (fun p : ℝ^n × ℝ ↦ nonhomogeneousSolution f p.1 p.2) ∧
    ContDiffOn ℝ 1 (fun p : ℝ^n × ℝ ↦ nonhomogeneousSolution f p.1 p.2)
      (univ ×ˢ Ioi 0) ∧
    (∀ t : ℝ, ContDiff ℝ 2 (fun x ↦ nonhomogeneousSolution f x t)) ∧
    (∀ i j : Fin n, Continuous (fun p : ℝ^n × ℝ ↦
      (∂[i] (∂[j] (fun x ↦ nonhomogeneousSolution f x p.2))) p.1)) ∧
    (∀ (x : ℝ^n) (t : ℝ), 0 < t →
      deriv (fun τ ↦ nonhomogeneousSolution f x τ) t -
        laplacian (fun y ↦ nonhomogeneousSolution f y t) x = f (timeSpaceCons t x)) ∧
    (∀ x : ℝ^n, nonhomogeneousSolution f x 0 = 0) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (x : ℝ^n) (t : ℝ), 0 < t → t < δ →
        |nonhomogeneousSolution f x t| < ε := by
  let g : ℝ → ℝ^n → ℝ := fun s x ↦ f (timeSpaceCons (max 0 s) x)
  have hclamp : Continuous (fun p : ℝ × ℝ^n ↦
      ((⟨max 0 p.1, le_max_left (0 : ℝ) p.1⟩ : Ici (0 : ℝ)), p.2)) :=
    ((continuous_const.max continuous_fst).subtype_mk _).prodMk continuous_snd
  have hg : Continuous (Function.uncurry g) := hf.comp hclamp
  have hg2 (s : ℝ) : ContDiff ℝ 2 (g s) := hf2 _ (le_max_left _ _)
  have hgc (s : ℝ) : HasCompactSupport (g s) :=
    hfc.slice_snd ⟨max 0 s, le_max_left (0 : ℝ) s⟩
  have hgfirst (i : Fin n) : Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (g p.1)) p.2) :=
    (hfirst i).comp hclamp
  have hgsecond (i j : Fin n) : Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (∂[j] (g p.1))) p.2) :=
    (hsecond i j).comp hclamp
  obtain ⟨M, C, B, hM, hC, hB⟩ :=
    PDE.FDeriv.exists_uniform_spatial_jet_bounds _ hf hfc hfirst hsecond
  have hgM (s : ℝ) (x : ℝ^n) : ‖g s x‖ ≤ M :=
    hM (⟨max 0 s, le_max_left (0 : ℝ) s⟩, x)
  have hgC (i : Fin n) (s : ℝ) (x : ℝ^n) : ‖(∂[i] (g s)) x‖ ≤ C i :=
    hC i (⟨max 0 s, le_max_left (0 : ℝ) s⟩, x)
  have hgB (i j : Fin n) (s : ℝ) (x : ℝ^n) :
      ‖(∂[i] (∂[j] (g s))) x‖ ≤ B i j :=
    hB i j (⟨max 0 s, le_max_left (0 : ℝ) s⟩, x)
  have heq (x : ℝ^n) (t : ℝ) :
      nonhomogeneousSolution f x t =
        ∫ s in 0..max 0 t, initialValueSolution (g s) x (max 0 t - s) :=
    nonhomogeneousSolution_eq_intervalIntegral_clamp f x t
  have hslice (t : ℝ) : (fun x ↦ nonhomogeneousSolution f x t) =
      (fun x ↦ ∫ s in 0..max 0 t, initialValueSolution (g s) x (max 0 t - s)) :=
    funext fun x ↦ heq x t
  have hpositive (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
      nonhomogeneousSolution f x t =
        ∫ s in 0..t, initialValueSolution (g s) x (t - s) := by
    simpa only [max_eq_right ht.le] using heq x t
  refine ⟨?_, ?_, ?_, ?_, ?_, nonhomogeneousSolution_initial_value f, ?_⟩
  · exact ((continuous_integral_initialValueSolution_family g hg hgM).comp
      (continuous_fst.prodMk (continuous_const.max continuous_snd))).congr
        (fun p ↦ (heq p.1 p.2).symm)
  · exact (contDiffOn_one_integral_initialValueSolution
      g hg hg2 hgc hgM hgfirst C hgC (fun i ↦ hgsecond i i)
        (fun i ↦ B i i) (fun i ↦ hgB i i)).congr
          (fun p hp ↦ hpositive p.1 p.2 hp.2)
  · intro t
    rw [hslice]
    exact contDiff_two_integral_initialValueSolution_space
      g hg hg2 hgc hgM hgfirst C hgC hgsecond B hgB (max 0 t)
  · intro i j
    simp_rw [hslice]
    exact (continuous_secondPartial_integral_initialValueSolution
      g hg hg2 hgc hgM hgfirst C hgC hgsecond B hgB i j).comp
        (continuous_fst.prodMk (continuous_const.max continuous_snd))
  · intro x t ht
    have htime : (fun τ ↦ nonhomogeneousSolution f x τ) =ᶠ[𝓝 t]
        (fun τ ↦ ∫ s in 0..τ, initialValueSolution (g s) x (τ - s)) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with τ hτ
      exact hpositive x τ hτ
    rw [htime.deriv_eq, hslice, max_eq_right ht.le]
    simpa only [laplacian, g, max_eq_right ht.le] using
      integral_initialValueSolution_forced_heat_residual
        g hg hg2 hgc hgM hgfirst C hgC hgsecond B hgB x t ht
  · exact nonhomogeneousSolution_uniform_initial_trace f M
      (fun s hs ↦ (hf2 s hs).continuous)
      (fun s hs x ↦ by simpa only [Real.norm_eq_abs] using hM (⟨s, hs⟩, x))

end HeatEquation
