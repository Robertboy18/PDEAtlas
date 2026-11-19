/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Definitions
public import PDE.DistributionTheory.TestFunction.CompactCutoff
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

/-!
# Uniform approximation of zero-boundary data

A continuous function on a bounded domain closure, zero on its frontier, extends
continuously by zero. Smooth approximation of that extension, followed by a cutoff
on the compact set where the datum is appreciable, gives compactly supported smooth
approximations inside the domain. No boundary regularity is needed.
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open SobolevSpace SobolevSpace.GraphSpace Set
open scoped ContDiff

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Continuous zero-boundary data on a bounded open domain can be uniformly approximated
on its closure by smooth functions compactly supported inside the domain. -/
theorem exists_testFunction_uniform_approximation
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, g x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : TestFunctionOn n Ω, ∀ x ∈ closure Ω, |φ.1.toFun x - g x| < ε := by
  classical
  let u := Ω.piecewise g 0
  have hu : Continuous u := continuous_piecewise hzero hg continuousOn_const
  have huc : HasCompactSupport u :=
    HasCompactSupport.of_support_subset_isCompact hbounded.isCompact_closure fun x hx ↦
      by_contra fun hc ↦ hx (piecewise_eq_of_notMem Ω g 0 fun hi ↦ hc (subset_closure hi))
  have hug (x : ℝ^n) (hx : x ∈ closure Ω) : u x = g x := by
    by_cases hi : x ∈ Ω
    · exact piecewise_eq_of_mem Ω g 0 hi
    · rw [show u x = 0 from piecewise_eq_of_notMem Ω g 0 hi, hzero x
        (by rw [hopen.frontier_eq]; exact ⟨hx, hi⟩ : x ∈ frontier Ω)]
  let K := closure Ω ∩ {x | ε / 2 ≤ |u x|}
  have hK : IsCompact K := hbounded.isCompact_closure.inter_right
    (isClosed_le continuous_const hu.abs)
  have hKΩ : K ⊆ Ω := fun x hx ↦ by
    by_contra hi
    have hb : ε / 2 ≤ |u x| := hx.2
    rw [show u x = 0 from piecewise_eq_of_notMem Ω g 0 hi, abs_zero] at hb
    linarith
  obtain ⟨η, hηΩ, hηone, _, hηrange⟩ :=
    TestFunction.exists_eq_one_on_compact hopen hK hKΩ
  obtain ⟨F, hF, hFu⟩ :=
    (huc.uniformContinuous_of_continuous hu).exists_contDiff_dist_le (half_pos hε)
  let φ : TestFunctionOn n Ω := ⟨⟨fun x ↦ η.toFun x * F x,
    η.contDiff.mul hF, η.hasCompactSupport.mul_right, subset_univ _⟩,
    tsupport_mul_subset_left.trans hηΩ⟩
  refine ⟨φ, fun x hx ↦ ?_⟩
  change |η.toFun x * F x - g x| < ε
  rw [← hug x hx]
  have herr : |F x - u x| < ε / 2 := by simpa only [Real.dist_eq] using hFu x
  by_cases hlarge : ε / 2 ≤ |u x|
  · rw [hηone x ⟨hx, hlarge⟩, one_mul]
    exact herr.trans (half_lt_self hε)
  · have hsmall := lt_of_not_ge hlarge
    obtain ⟨hη0, hη1⟩ := hηrange x
    calc
      |η.toFun x * F x - u x| =
          |η.toFun x * (F x - u x) + (η.toFun x - 1) * u x| := by ring_nf
      _ ≤ |η.toFun x| * |F x - u x| + |η.toFun x - 1| * |u x| := by
        simpa only [abs_mul] using abs_add_le
          (η.toFun x * (F x - u x)) ((η.toFun x - 1) * u x)
      _ ≤ 1 * |F x - u x| + 1 * |u x| := by
        gcongr
        · exact abs_le.2 ⟨by linarith, hη1⟩
        · exact abs_le.2 ⟨by linarith, by linarith⟩
      _ < ε := by linarith

end HeatEquation
